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
  private type StringE[B] = String \/ B
  private type TProcess[A] = Process[Task, A]
  private val pmn = helper.processMonad[Nothing]
  private val pmt = helper.processMonad[Task]

  //TODO Implement clean up function of heap, that removes unneeded constraints

  //TODO Convert use of SetLit to use of Process0[Symbols] and results to Process0[String \/ Symbols]
  def match_it(set : SetLit, c : Class, heap: SHeap): String \/ SetLit = set.es.toList.traverseU {
    case Symbol(ident) => for {
      symv <- heap.spatial.get(ident).cata(_.right, s"Unknown symbol: $ident".left)
      stc <- defs.subtypesOrSelf.get(c).cata(cs => cs.right, s"Unknown class: $c".left)
    } yield if (stc.contains(_sd_c.get(symv))) List[BasicExpr](Symbol(ident)) else List()
    case Var(name) => s"Unevaluated var $name".left
  }.map(l => SetLit(l.join : _*))

  def descendants_or_self(set : SetLit, heap: SHeap): String \/ SetLit = set.es.toList.traverseU {
    case e@Symbol(ident) => for {
      symv <- heap.spatial.get(ident).cata(_.right, s"Unknown symbol: $ident".left)
      cd <- _sd_concrete.getOption(symv).cata(_.right, s"Not a concrete value: $symv".left)
      res <- cd.children.values.toList.map(s => SetNormalizer.normalize(heap.pure).apply(s).get).traverseU({
        case chldv: SetLit => descendants_or_self(chldv, heap)
        case e2 => s"Not a concrete set: $e2".left
      }).map(l => l.flatMap(_.es))
    } yield e :: res
    case Var(name) => s"Unevaluated var $name".left
  }.map(l => SetLit(l.join :_*))

  def match_star(set : SetLit, c : Class, heap : SHeap): String \/ SetLit =
    for {
      dcs <- descendants_or_self(set, heap)
      m <- match_it(dcs, c, heap)
    } yield m

  def unfold(sym : Symbols, sd : SpatialDesc, heap: SHeap): Process0[String \/ (ConcreteDesc, SHeap)] = {
    def all_children(c : Class) : Map[Fields, (Class, Cardinality)] = {
      val defc = defs(c)
      defc.children ++ defc.superclass.map(all_children).getOrElse(Map())
    }
    def all_references(c : Class) : Map[Fields, (Class, Cardinality)] = {
      val defc = defs(c)
      defc.refs ++ defc.superclass.map(all_references).getOrElse(Map())
    }
    def freshSet(cl : Class, card : Cardinality) : List[(SetExpr, Spatial[Symbols], Set[QSpatial])] = {
      card match {
        case Single => {
          val sym = freshSym
          List((SetLit(Symbol(sym)), Map(sym -> AbstractDesc(cl)), Set[QSpatial]()))
        }
        case Many => {
          val sym = SetSymbol((cl, Many), freshSym)
          List((sym, Map[Symbols, SpatialDesc](), Set(QSpatial(sym, cl))))
        }
        case Opt => {
          val sym = SetSymbol((cl, Opt), freshSym)
          List((sym, Map[Symbols, SpatialDesc](), Set(QSpatial(sym, cl))))
        }
      }
    }

    sd match {
      case AbstractDesc(c) =>
        for {
           defc <- Process(defs.get(c).cata(_.right, s"Class definition of $c is unknown".left))
           // Type inference is a bit limited for higher-kinded types
           sts <- defc.traverse(dc => Process((defs.subtypesOrSelf(Class(dc.name))).toList : _*))(pmn)
           cdc <- sts.traverse[Process0, String, (ConcreteDesc, SHeap)](st => for {
                     cs <- Process(all_children(st).mapValues(v => freshSet(v._1, v._2)).sequenceU :_*)
                     rs  <- Process(all_references(st).mapValues(v => freshSet(v._1, v._2)).sequenceU :_*)
                     chlds = cs.mapValues(_._1)
                     refs  = rs.mapValues(_._1)
                     all = cs.values.toList ++ rs.values.toList
                     (_, newspatials, newqspatials) = all.unzip3(identity)
                     newspatial = newspatials.foldLeft(Map[Symbols, SpatialDesc]())(_ ++ _)
                     newqspatial = newqspatials.foldLeft(Set[QSpatial]())(_ ++ _)
                     cd = ConcreteDesc(st, chlds, refs)
                   } yield (cd, (_sh_spatial.modify(_.updated(sym, cd) ++ newspatial) `andThen` _sh_qspatial.modify(_ ++ newqspatial))(heap)))(pmn)
        } yield cdc
      case cd@ConcreteDesc(c, children, refs) => Process((cd, heap).right)
    }
  }

  def unfold_all(syms : SetLit, heap: SHeap): Process0[String \/ SHeap] = {
    syms.es.toList.foldLeft[Process0[String \/ SHeap]](Process(heap.right))((heaps: Process0[String \/ SHeap], b : BasicExpr) =>
      for {
        he <- heaps
        newheaps <- he.flatMap(h => (for {
           sym <- getSymbol(SetLit(b))
           _ = println(PrettyPrinter.pretty(h))
           symv <- h.spatial.get(sym).cata(_.right, s"Unknown symbol: ${PrettyPrinter.pretty(Symbol(sym))}".left)
           newheaps = unfold(sym, symv, h)
        } yield newheaps)).traverse(identity)(pmn).map(_.join.map(_._2))
      } yield newheaps)
  }

  def concretise(el: SetLit, heap: SHeap): Process[Task, String \/ SHeap] = {
    def concretise_final(el: SetLit, heap: SHeap): Process0[SHeap] = {
      Process((el.es.foldLeft(heap.some) { (h: Option[SHeap], b: BasicExpr) =>
        for {
          hh <- h
          sym <- b match {
            case Symbol(id) => id.some
            case Var(name) => none
          }
          symv <- hh.spatial.get(sym)
          cd <- _sd_concrete.getOption(symv)
          defc <- defs.get(cd.c)
          if defc.children.values.forall(_._2.isOptional)
        } yield _sh_spatial.modify(_.updated(sym, _cd_children.modify(_.mapValues(v => SetLit()))(cd)))(hh)
      }).toSeq : _*)
    }
    // TODO Convert all SetLit to expression
    def concretise_helper(el: SetLit, heap: SHeap, depth: Int): Process[Task, String \/ SHeap] = {
      if (depth <= 0) {
        concretise_final(el, heap).map(_.right)
      }
      else for {
        unfolded <- unfold_all(el, heap)
        res <- unfolded.traverse[TProcess, String, String \/ SHeap](h => {
          val childsyms = el.es.flatMap(e =>
            e.asInstanceOf[Symbol].id.|>(h.spatial.get)
              .flatMap(_sd_concrete.getOption).map(_.children.values).get)
          // Just join everything together
          val joinede = childsyms.foldLeft(SetLit() : SetExpr)(Union)
          for {
            joinedset_th <- mf.findSet(joinede, h, beta)
            joinedset_heap = joinedset_th.map(kv =>
              (h.subst_all(kv._1) |> expand, kv._2))
            cfinal = concretise_final(el, h).map(_.right)
            cfurther = joinedset_heap.traverse[TProcess, String, String \/ SHeap](
              ((hhh : SHeap, els : SetLit) => concretise_helper(els, hhh, depth - 1)).tupled).map(_.join)
            concretised <- cfinal ++ cfurther
          } yield concretised
        })(pmt).map(_.join)
      } yield res
    }
    concretise_helper(el, heap, delta)
  }

  def access(sym: Symbols, f: Fields, heap: SHeap): Process0[String \/ (SetExpr, SHeap)] = {
    for {
      symv <- Process(heap.spatial.get(sym).cata(_.right, s"Error, unknown symbol $sym".left))
      unfolded <- symv.traverse(desc => unfold(sym, desc, heap))(pmn).map(_.join)
      res = unfolded.traverseU(unf => {
        val (df, newheap) = unf
        if (defs.childfields.contains(f))
          for (chld <- df.children.get(f)) yield (chld, newheap)
        else if (defs.reffields.contains(f))
          for (ref <- df.refs.get(f)) yield (ref, newheap)
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

  def update(sym: Symbols, f: Fields, ee2: SetExpr, heap: SHeap): Process0[String \/ SHeap] = {
    for {
      symv <- Process(heap.spatial.get(sym).cata(_.right, s"Error, unknown symbol $sym".left))
      unfolded <- symv.traverse(desc => unfold(sym, desc, heap))(pmn).map(_.join)
      res = unfolded.traverseU(unf => {
        val (df, newheap) = unf
        if (defs.childfields.contains(f)) for {
          _ <- df.children.get(f).cata(_.right, s"Error, field $f not allocated for symbol $sym".left)
        } yield _sh_spatial.modify(_.updated(sym, _cd_children.modify(_.updated(f, ee2))(df)))(disown(newheap, ee2))
        else if (defs.reffields.contains(f)) for {
          _ <- df.refs.get(f).cata(_.right, s"Error, field $f not allocated for symbol $sym".left)
        } yield _sh_spatial.modify(_.updated(sym, _cd_refs.modify(_.updated(f, ee2))(df)))(newheap)
        else s"Field $f is neither a child nor a reference field".left
      })
    } yield res.join
  }

  def expand(heap: SHeap): SHeap = {
    val (newspatial, newqspatial) = heap.qspatial.foldLeft((heap.spatial, Set[QSpatial]())) {
      (part : (Spatial[Symbols], Set[QSpatial]), qs : QSpatial) => qs.e match {
          // TODO: Use String \/ - instead
        case SetLit(as @_*) =>
          val expanded: Map[Symbols, SpatialDesc] =
            as.map(_.asInstanceOf[Symbol]).map(_.id -> _sd_abstract.reverseGet(AbstractDesc(qs.c))).toMap
          // TODO: Consider a good way to merge things
          (part._1 ++ expanded, part._2)
        case _ => (part._1, part._2 + qs)
      }
    }
    SHeap(newspatial, newqspatial, heap.pure)
  }

  def execute(pres : Process[Task, SMem], c : Statement) : Process[Task, String \/ SMem] = {
    // Todo parallelise using mergeN
    pres.flatMap { (pre: SMem) =>
      if (!hcc.isConsistent(pre.heap)) Process(s"Inconsistent memory ${PrettyPrinter.pretty(pre.heap)}".left)
      else c match {
        case StmtSeq(_,ss@_*) => ss.toList.foldLeft[Process[Task, String \/ SMem]](Process(pre.right))(
          (pmem, s) => for {
            memr <- pmem
            res <- memr.traverse[TProcess, String, String \/ SMem](mem =>
               execute(Process(mem), s)).map(_.join)
          } yield res)
        case AssignVar(_,x, e) => Process(for {
          ee <- evalExpr(pre.stack, e)
        } yield _sm_stack.modify(_ + (x -> ee))(pre))
        case New(_, x, c) => Process(for {
          cdef <- defs.get(c).cata(_.right, s"Unknown class: $c".left)
          xsym = freshSym
          alloced =
              xsym -> ConcreteDesc(c, cdef.children.mapValues(_ => SetLit()), cdef.refs.mapValues(_ => SetLit()))
        } yield (_sm_stack.modify(_ + (x -> SetLit(Symbol(xsym)))) `andThen`
                      (_sm_heap ^|-> _sh_spatial).modify(_ + alloced))(pre))
        case LoadField(_, x, e, f) => for {
          sym <- Process(evalExpr(pre.stack, e).flatMap(getSymbol))
          ares <- sym.traverse[TProcess, String, String \/ (SetExpr, SHeap)](s =>
                  access(s, f, pre.heap))(pmt).map(_.join)
        } yield ares.map(p => SMem(pre.stack + (x -> p._1), p._2))
        case AssignField(_, e1, f, e2) => {
          evalExpr(pre.stack, e1).flatMap(getSymbol).traverse[TProcess, String, String \/ SMem](sym =>
              evalExpr(pre.stack, e2).traverse[TProcess, String, String \/ SMem](ee2 =>
                    for {
                       newheaps <- update(sym, f, ee2, pre.heap)
                    } yield newheaps.map(_sm_heap.set(_)(pre))
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
            posts <- cstmt.traverse[TProcess, String, String \/ SMem]( cst => {
                val (eb, s) = cst
                val newmem = (_sm_heap ^|-> _sh_pure).modify(_ + eb)(pre)
                execute(Process(newmem), s)
            }).map(_.join)
          } yield posts
        }
        case For(_, x, m, sb) => for {
           // TODO: Figure out how to get meaningful set with new symbols that don't point in the heap for references
            esolr <- evalExpr(pre.stack, _me_e.get(m)).traverse[TProcess, String, String \/ (Map[Symbols, SetLit], SetLit)](ee =>
               mf.findSet(ee, pre.heap, beta)).map(_.join)
            res <- esolr.traverse[TProcess, String, String \/ SMem](esol => {
                val (th, ees) = esol
                val newpre = pre.subst_all(th) |> _sm_heap.modify(expand)
                for {
                  mres  <- m match {
                    case MSet(e) => Process((ees, newpre).right)
                    case Match(e, c) => for {
                       heapr <- unfold_all(ees, newpre.heap)
                       res = heapr.flatMap(h => for {
                          matches <- match_it(ees, c, h)
                       } yield (matches, h))
                    } yield res.map(p => (p._1, _sm_heap.set(p._2)(newpre)))
                    case MatchStar(e, c) => for {
                      heapr <- concretise(ees, newpre.heap)
                      res = heapr.flatMap(h => for {
                        matches <- match_star(ees, c, h)
                      } yield (matches, h))
                    } yield res.map(p => (p._1, _sm_heap.set(p._2)(newpre)))
                  }
                  res <- mres.traverse[TProcess, String, String \/ SMem](mr => {
                    val (syms, pre) = mr
                    syms.es.toList.foldLeft[Process[Task, String \/ SMem]](Process(pre.right))((memp : Process[Task, String \/ SMem], sym : BasicExpr) =>
                      for {
                        memr <- memp
                        res <- memr.traverse[TProcess, String, String \/ SMem](nmem =>
                          execute(Process(_sm_stack.modify(_ + (x -> SetLit(sym)))(nmem)), sb)
                        )(pmt).map(_.join)
                      } yield res
                    )
                  })(pmt).map(_.join)
                } yield res
              })(pmt).map(_.join)
        } yield res
        case Fix(_, e, sb) => {
          def fixEqCase(bmem: SMem): Process[Task, String \/ SMem] = {
            for {
              sbr <- execute(Process(bmem), sb)
              res = for {
                  amem <- sbr
                  eeb <- evalExpr(bmem.stack, e)
                  eea <- evalExpr(amem.stack, e)
                } yield (_sm_heap ^|-> _sh_pure).modify(_ + Eq(eeb, eea))(amem)
            } yield res
          }
          def fixNeqCase(bmem: SMem, k: Int): Process[Task, String \/ SMem] = {
            for {
              sbr <- execute(Process(bmem), sb)
              imem2r = for {
                imem <- sbr
                eeb <- evalExpr(bmem.stack, e)
                eei <- evalExpr(imem.stack, e)
              } yield (_sm_heap ^|-> _sh_pure).modify(_ + Not(Eq(eeb, eei)))(imem)
              res <- imem2r.traverse[TProcess, String, String \/ SMem](imem =>
                if (k <= 0) fixEqCase(imem) else fixEqCase(imem) ++ fixNeqCase(imem, k - 1)
              ).map(_.join)
            } yield res
          }
          fixEqCase(pre) ++ fixNeqCase(pre, kappa)
        }
      }
    }
  }

  def getSymbol(e : SetExpr): String \/ Symbols = {
    e match {
      case SetLit(Symbol(sym)) => sym.right
      case _ => s"${PrettyPrinter.pretty(e)} is not a symbol".left
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

  private val mf = new ModelFinder(symCounter, defs)

  private val hcc = new HeapConsistencyChecker(defs)

}
