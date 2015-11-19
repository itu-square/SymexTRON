package semantics

import scala.language.postfixOps

import syntax.ast.MatchExpr._
import syntax.PrettyPrinter
import syntax.ast.ConcreteDesc._
import syntax.ast.QSpatial._
import syntax.ast.SHeap._
import syntax.ast.SMem._
import syntax.ast.SpatialDesc._
import helper._
import semantics.Subst._
import syntax.ast._

import scalaz._, Scalaz._
import scalaz.stream._
import scalaz.concurrent.Task
import monocle.syntax._
import monocle.function._
import monocle.std.tuple2._

class SymbolicExecutor(defs: Map[Class, ClassDefinition],
                       kappa: Int = 3, delta: Int = 3, beta: Int = 5) {

  //TODO Implement clean up function of heap, that removes unneeded constraints

  //TODO Convert use of SetLit to use of Process0[Symbols] and results to Process0[String \/ Symbols]
  def match_it(set : SetLit, c : Class, heap: SHeap): String \/ SetLit = set.es.toList.traverseU {
    case Symbol(ident) => for {
      symv <- heap.spatial.get(ident).cata(_.right, s"Unknown symbol: $ident".left)
      stc <- defs.subtypesOrSelf.get(c).cata(cs => cs.right, s"Unknown class: $c".left)
    } yield if (stc.contains(_sd_c.get(symv))) List[BasicExpr](Symbol(ident)) else List()
    case Var(name) => s"Unevaluated var $name".left
  }.map(l => SetLit(l.join : _*))

  def descendants_or_self(set : SetLit, c : Class, heap: SHeap): String \/ SetLit = {
    set.es.toList.traverseU {
      case e@Symbol(ident) => for {
        symv <- heap.spatial.get(ident).cata(_.right, s"Unknown symbol: $ident".left)
        cd <- _sd_concrete.getOption(symv).cata(_.right, s"Not a concrete value: ${PrettyPrinter.pretty(Map(ident -> symv))} in heap \n\n${PrettyPrinter.pretty(heap)}\n\n".left)
        res <- if (defs.canContain(cd.c, c)) cd.children.values.toList.traverseU({
          case chldv: SetLit => descendants_or_self(chldv, c, heap)
          case e2 => s"Not a concrete set: $e2".left
        }).map(l => l.flatMap(_.es)) else List().right
      } yield e :: res
      case Var(name) => s"Unevaluated var $name".left
    }.map(l => SetLit(l.join :_*))
  }

  def match_star(set : SetLit, c : Class, heap : SHeap): String \/ SetLit =
    for {
      dcs <- descendants_or_self(set, c, heap)
      m <- match_it(dcs, c, heap)
    } yield m


  def access(sym: Symbols, f: Fields, initialHeap: SHeap, currentHeap: SHeap): Process0[String \/ (SetExpr, SHeap, SHeap)] = {
    for {
      symv <- Process(currentHeap.spatial.get(sym).cata(_.right, s"Error, unknown symbol $sym".left))
      unfolded <- symv.traverse(desc => modelFinder.unfold(sym, desc, initialHeap, currentHeap))(pmn).map(_.join)
      res = unfolded.traverseU(unf => {
        val (df, newiheap, newcheap) = unf
        if (defs.childfields.contains(f))
          for (chld <- df.children.get(f)) yield (chld, newiheap, newcheap)
        else if (defs.reffields.contains(f))
          for (ref <- df.refs.get(f)) yield (ref, newiheap, newcheap)
        else none
      }.cata(_.right, s"No value for field $f".left))
    } yield res.join
  }

  def disown(heap: SHeap, ee: SetExpr) : SHeap = {
    def disownSD(sym: Symbols, desc: SpatialDesc): SHeap => SHeap  = desc match {
      case cd@ConcreteDesc(c, children, refs) => {
        val (newchildren, newconstrs) =
          children.foldLeft((Map[String, SetExpr](), Set[BoolExpr]()))(
            (st, chld) => {
              val preve = chld._2
              //TODO Handle safely and find more precise type by infering on preve
              val symt = defs.fieldType(c, chld._1).get
              val ssym1 = SetSymbol(symt, freshSym)
              val ssym2 = SetSymbol(symt, freshSym)
              val cstrs =
                   Set(Eq(preve, Union(ssym1, ssym2)),
                    Eq(ISect(ssym1, ssym2), SetLit()),
                    SetSubEq(ssym2, ee),
                    Eq(ISect(ssym1, ee), SetLit()))
              st.applyLens(first).modify(_.updated(chld._1, ssym1))
                .applyLens(second).modify(_ ++ cstrs)
            }
          )
        _sh_pure.modify(_ ++ newconstrs) `andThen`
              _sh_spatial.modify(_.updated(sym,
                   cd.applyLens(_cd_children).set(newchildren)))
      }
      case _ => identity
    }

    // desc match {
    //   case ConcreteDesc(c, children, refs) => _sh_pure.modify(_ ++ (children.foldLeft(Set[BoolExpr]())(
    //                                                              (cstr : Prop, chld : (String, SetExpr)) => cstr + Eq(ISect(chld._2, ee), SetLit()))))
    // }
    // TODO consider types when disowning things
    (((h : SHeap) => h.spatial.foldLeft(identity[SHeap] _)((f : SHeap => SHeap, el : (Symbols, SpatialDesc)) =>
        f `andThen` (disownSD _).tupled(el))(h))) (heap)
  }

  def update(sym: Symbols, f: Fields, ee2: SetExpr, initialHeap: SHeap, currentHeap: SHeap): Process0[String \/ (SHeap, SHeap)] = {
    for {
      symv <- Process(currentHeap.spatial.get(sym).cata(_.right, s"Error, unknown symbol $sym".left))
      unfolded <- symv.traverse(desc => modelFinder.unfold(sym, desc, initialHeap, currentHeap))(pmn).map(_.join)
      res = unfolded.traverseU { unf =>
        val (df, newiheap, newcheap) = unf
        if (defs.childfields.contains(f)) for {
          _ <- df.children.get(f).cata(_.right, s"Error, field $f not allocated for symbol $sym".left)
        } yield (newiheap,
            _sh_spatial.modify(_.updated(sym, _cd_children.modify(_.updated(f, ee2))(df)))(disown(newcheap, ee2)))
        else if (defs.reffields.contains(f)) for {
          _ <- df.refs.get(f).cata(_.right, s"Error, field $f not allocated for symbol $sym".left)
        } yield (newiheap,
            _sh_spatial.modify(_.updated(sym, _cd_refs.modify(_.updated(f, ee2))(df)))(newcheap))
        else s"Field $f is neither a child nor a reference field".left
      }
    } yield res.join
  }

  def execute(pres : Set[SMem], c : Statement): Process[Task, String \/ (SMem, SMem)] = {
     executeHelper(Process.emitAll(pres.toSeq).map(pre => (pre, pre)), c)
  }

  private def isConsistent(initHeap: SHeap, curHeap: SHeap) = {
    heapConsistencyChecker.isConsistent(initHeap) &&
      heapConsistencyChecker.isConsistent(curHeap)
  }

  private def executeHelper(pres : Process[Task, (SMem, SMem)], c : Statement) : Process[Task, String \/ (SMem, SMem)] = {
    // Todo parallelise using mergeN
    pres.flatMap { case (initMem: SMem, pre: SMem) =>
      if (!isConsistent(initMem.heap, pre.heap)) Process(s"Inconsistent memory ${PrettyPrinter.pretty(pre.heap)}".left)
      else c match {
        case StmtSeq(_,ss@_*) => ss.toList.foldLeft[Process[Task, String \/ (SMem, SMem)]](Process((initMem, pre).right))(
          (pmem, s) => for {
            memr <- pmem
            res <- memr.traverse[TProcess, String, String \/ (SMem, SMem)](mem =>
               executeHelper(Process(mem), s)).map(_.join)
          } yield res)
        case AssignVar(_,x, e) => Process(for {
          ee <- evalExpr(pre.stack, e)
        } yield (initMem, _sm_stack.modify(_ + (x -> ee))(pre)))
        case New(_, x, c) => Process(for {
          cdef <- defs.get(c).cata(_.right, s"Unknown class: $c".left)
          xsym = freshSym
          alloced =
              xsym -> ConcreteDesc(c, cdef.children.mapValues(_ => SetLit()), cdef.refs.mapValues(_ => SetLit()))
        } yield (initMem, (_sm_stack.modify(_ + (x -> SetLit(Symbol(xsym)))) `andThen`
                      (_sm_heap ^|-> _sh_spatial).modify(_ + alloced))(pre)))
        case LoadField(_, x, e, f) => for {
          sym <- Process(evalExpr(pre.stack, e).flatMap(getSingletonSymbolId))
          ares <- sym.traverse[TProcess, String, String \/ (SetExpr, SHeap, SHeap)](s =>
                  access(s, f, initMem.heap, pre.heap))(pmt).map(_.join)
        } yield ares.map(p => (SMem(initMem.stack, p._2), SMem(pre.stack + (x -> p._1), p._3)))
        case AssignField(_, e1, f, e2) => {
          evalExpr(pre.stack, e1).flatMap(getSingletonSymbolId).traverse[TProcess, String, String \/ (SMem, SMem)](sym =>
              evalExpr(pre.stack, e2).traverse[TProcess, String, String \/ (SMem, SMem)](ee2 =>
                    for {
                       newheaps <- update(sym, f, ee2, initMem.heap, pre.heap)
                    } yield newheaps.map { case (newiheap, newcheap) => (_sm_heap.set(newiheap)(initMem), _sm_heap.set(newcheap)(pre)) }
              )(pmt).map(_.join)
          )(pmt).map(_.join)
        }
        case If(_, ds, cs@_*) =>{
          val ecs    = cs.map(p => evalBoolExpr(pre.stack, p._1).map((_, p._2))).toList
          val elsecase = for {
            other <- ecs.traverseU(_.map(_._1))
          } yield other.map(not).foldLeft[BoolExpr](True)(And(_,_)) -> ds
          val newecs = Process((elsecase :: ecs) : _*)
          for {
            cstmt <- newecs
            posts <- cstmt.traverse[TProcess, String, String \/ (SMem, SMem)](cst => {
                val (eb, s) = cst
                val newmem = (_sm_heap ^|-> _sh_pure).modify(_ + eb)(pre)
                executeHelper(Process((initMem, newmem)), s)
            }).map(_.join)
          } yield posts
        }
        case For(_, x, m, sb) => for {
           // TODO: Figure out how to get meaningful set with new symbols that don't point in the heap for references
            esolr <- evalExpr(pre.stack, _me_e.get(m)).traverse[TProcess, String, String \/ (Map[Symbols, SetLit], SetLit)](ee =>
               modelFinder.findSet(ee, pre.heap, beta)).map(_.join)
            res <- esolr.traverse[TProcess, String, String \/ (SMem, SMem)](esol => {
                val (th, ees) = esol
                val newpre = modelFinder.applySubst(th, pre)
                val newinitMem = modelFinder.applySubst(th, initMem)
                // TODO Somewhat inefficient, optimize
                for {
                  mres  <- (m match {
                    case MSet(e) =>
                        //if (isConsistent(newinitMem.heap, newpre.heap))
                        Process((ees, newinitMem, newpre).right)
                        //else Process()
                    case Match(e, c) => for {
                       heapr <- modelFinder.unfold_all(ees, newinitMem.heap, newpre.heap)
                       res = heapr/*.filter((isConsistent _).tupled)*/.flatMap { case (ih, ch) => for {
                          matches <- match_it(ees, c, ch)
                       } yield (matches, ih, ch) }
                    } yield res.map(p => (p._1, _sm_heap.set(p._2)(newinitMem), _sm_heap.set(p._3)(newpre)))
                    case MatchStar(e, c) => for {
                      memr <- modelFinder.concretise(ees, newinitMem, newpre, c = c.some)
                      res = memr/*.filter{ case (im, cm) => isConsistent(im.heap, cm.heap)
                                 }*/.flatMap { case (initMem, curMem) => for {
                        matches <- match_star(ees, c, curMem.heap)
                      } yield (matches, initMem, curMem) }
                    } yield res
                  })
                  res <- mres.traverse[TProcess, String, String \/ (SMem, SMem)](mr => {
                    val (syms, initMem, pre) = mr
                    syms.es.toList.foldLeft[Process[Task, String \/ (SMem, SMem)]](Process((initMem, pre).right))((memp : Process[Task, String \/ (SMem, SMem)], sym : BasicExpr) =>
                      for {
                        memr <- memp
                        res <- memr.traverse[TProcess, String, String \/ (SMem, SMem)]{ case (ninitMem, nmem) =>
                          executeHelper(Process((ninitMem, _sm_stack.modify(_ + (x -> SetLit(sym)))(nmem))), sb)
                        }(pmt).map(_.join)
                      } yield res
                    )
                  })(pmt).map(_.join)
                } yield res
              })(pmt).map(_.join)
        } yield res
        case Fix(_, e, sb) => {
          def fixEqCase(initMem: SMem, bmem: SMem): Process[Task, String \/ (SMem, SMem)] = {
            for {
              sbr <- executeHelper(Process((initMem, bmem)), sb)
              res = for {
                  pmem <- sbr
                  (initMem, amem) = pmem
                  eeb <- evalExpr(bmem.stack, e)
                  eea <- evalExpr(amem.stack, e)
                } yield (initMem, (_sm_heap ^|-> _sh_pure).modify(_ + Eq(eeb, eea))(amem))
            } yield res
          }
          def fixNeqCase(initMem: SMem, bmem: SMem, k: Int): Process[Task, String \/ (SMem, SMem)] = {
            for {
              sbr <- executeHelper(Process((initMem, bmem)), sb)
              imem2r = for {
                pmem <- sbr
                (initMem, imem) = pmem
                eeb <- evalExpr(bmem.stack, e)
                eei <- evalExpr(imem.stack, e)
              } yield (initMem, (_sm_heap ^|-> _sh_pure).modify(_ + Not(Eq(eeb, eei)))(imem))
              res <- imem2r.traverse[TProcess, String, String \/ (SMem, SMem)]{ case (initMem, imem) =>
                if (k <= 0) fixEqCase(initMem, imem) else fixEqCase(initMem, imem) ++ fixNeqCase(initMem, imem, k - 1)
              }.map(_.join)
            } yield res
          }
          fixEqCase(initMem, pre) ++ fixNeqCase(initMem, pre, kappa)
        }
      }
    }
  }

  def evalBasicExpr(s: SStack, e: BasicExpr): String \/ BasicExpr = e match {
    case Symbol(id) => Symbol(id).right
    case Var(name) =>
      s.get(name).cata({
            case SetLit(evalue) => evalue.right
            case ee => s"Not a basic expression: $ee".left
        }, s"Error while evaluating expression $e".left)
  }

  def evalExpr(s : SStack, e : SetExpr) : String \/ SetExpr = {
      e match {
        case SetLit(es @ _*) =>
          for {
            ees <- es.toList.traverseU(e => evalBasicExpr(s, e))
          } yield SetLit(ees : _*)
        case ssym : SetSymbol => ssym.right
        case SetVar(name) =>
          s.get(name).cata(_.right, s"Error while evaluating expression $e".left)
        case Diff(e1, e2) => for {
          ee1 <- evalExpr(s, e1)
          ee2 <- evalExpr(s, e2)
        } yield Diff(ee1, ee2)
        case Union(e1, e2) => for {
          ee1 <- evalExpr(s, e1)
          ee2 <- evalExpr(s, e2)
        } yield Union(ee1, ee2)
        case ISect(e1, e2) => for {
          ee1 <- evalExpr(s, e1)
          ee2 <- evalExpr(s, e2)
        } yield ISect(ee1, ee2)
      }
    }

  def evalBoolExpr(st : SStack, sp : BoolExpr) : String \/ BoolExpr = sp match {
    case Eq(e1, e2) =>
      for {
        ee1 <- evalExpr(st, e1)
        ee2 <- evalExpr(st, e2)
      } yield Eq(ee1, ee2)
    case ClassMem(e1, s) =>
      for {
        ee1 <- evalBasicExpr(st, e1)
      } yield ClassMem(ee1, s)
    case Not(p) =>
      for {
        ep <- evalBoolExpr(st, p)
      } yield Not(ep)
    case True => True.right
    case And(p1, p2) =>
      for {
        ep1 <- evalBoolExpr(st, p1)
        ep2 <- evalBoolExpr(st, p2)
      } yield And(ep1, ep2)
    case SetMem(e1, e2) =>
      for {
        ee1 <- evalBasicExpr(st, e1)
        ee2 <- evalExpr(st, e2)
      } yield SetMem(ee1, ee2)
    case SetSubEq(e1, e2) =>
      for {
        ee1 <- evalExpr(st, e1)
        ee2 <- evalExpr(st, e2)
      } yield SetSubEq(ee1, ee2)
  }


  private val symCounter = Counter(0)

  private def freshSym: Symbols = symCounter++

  val heapConsistencyChecker = new HeapConsistencyChecker(defs)

  val modelFinder = new ModelFinder(symCounter, defs, beta, delta)

}
