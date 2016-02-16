package semantics

import syntax.ast.MatchExpr._
import semantics.domains._
import semantics.domains.SHeap._
import semantics.domains.SMem._
import semantics.domains.SpatialDesc._
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
  def match_it(set : Set[Symbols], c : Class, heap: SHeap): String \/ Set[Symbols] = ???

  def descendants_or_self(set : Set[Symbols], c : Class, heap: SHeap): String \/ Set[Symbols] = ???

  def match_star(set : Set[Symbols], c : Class, heap : SHeap): String \/ Set[Symbols] =
    for {
      dcs <- descendants_or_self(set, c, heap)
      m <- match_it(dcs, c, heap)
    } yield m


  def access(sym: Symbol, f: Fields, heap: SHeap):
    Process0[String \/ (SetExpr[IsSymbolic.type], SHeap)] = {
    for {
      locr <- modelFinder.findLoc(sym, heap)
      unfolded <- locr.traverse({ case (loc, nheap) => modelFinder.unfold(loc, f, nheap) })(pmn).map(_.join)
      res = unfolded.flatMap { case (sdesc, nheap) =>
        if (defs.childfields.contains(f))
          (sdesc.children(f), nheap).right
        else if (defs.reffields.contains(f))
          (sdesc.refs(f), nheap).right
        else s"No value for field $f".left
      }
    } yield res
  }

  def disown(ee: SetExpr[IsSymbolic.type], loc: Loc, f: Fields, heap: SHeap) : SHeap =
    _sh_currentSpatial.modify(_ mapValuesWithKeys { case (loc2, sdesc) =>
        _sd_children.modify(_ mapValuesWithKeys { case (f2, ee2) =>
            if (loc2 == loc && f2 == f) ee2
            else {
              val t1opt = typeInference.inferSetType(ee, heap)
              val t2opt = typeInference.inferSetType(ee2, heap)
              t1opt.cata(t1 =>
                t2opt.cata(t2 =>
                  defs.maxClass(t1, t2).cata(_ => Diff(ee2, ee), ee2)
                , ee2)
              , ee2)
            }
        })(sdesc)
    })(heap)

  def update(sym: Symbol, f: Fields, ee: SetExpr[IsSymbolic.type], heap: SHeap): Process0[String \/ SHeap] = {
    for {
      locr <- modelFinder.findLoc(sym, heap)
      unfolded <- locr.traverse[({ type l[A] = Process[Nothing, A]})#l, String, String \/ (Loc, SpatialDesc, SHeap)]({ case (loc, nheap) =>
        for {
          unfoldedr <- modelFinder.unfold(loc, f, nheap)
        } yield unfoldedr.map { case (sdesc, nheap) => (loc, sdesc, nheap) }
      })(pmn).map(_.join)
      res = unfolded.flatMap { case (loc, sdesc, nheap) =>
        if (defs.childfields.contains(f)) {
          val nnheap = disown(ee, loc, f, nheap)
          _sh_currentSpatial.modify(_.updated(loc, _sd_children.modify(_.updated(f, ee))(sdesc)))(nnheap).right
        }
        else if (defs.reffields.contains(f))
          _sh_currentSpatial.modify(_.updated(loc, _sd_refs.modify(_.updated(f, ee))(sdesc)))(nheap).right
        else s"No value for field $f".left
      }
    } yield res
  }

  def execute(pres : Set[SMem], c : Statement): Process[Task, String \/ SMem] = {
     executeHelper(Process.emitAll(pres.toSeq), c)
  }

  private def executeHelper(pres : Process[Task, SMem], c : Statement) : Process[Task, String \/ SMem] = {
    // Todo parallelise using mergeN
    pres.flatMap[Task, String \/  SMem] { case (pre: SMem) =>
      if (!heapConsistencyChecker.isConsistent(pre.heap)) Process(s"Inconsistent memory ${PrettyPrinter.pretty(pre.heap)}".left)
      else c match {
        case StmtSeq(_,ss) => ss.toList.foldLeft[Process[Task, String \/ SMem]](Process(pre.right)) { (pmem, s) =>
          for {
            memr <- pmem
            res <- memr.traverse[TProcess, String, String \/ SMem](mem => executeHelper(Process(mem), s)).map(_.join)
          } yield res
        }
        case AssignVar(_,x, e) =>
          val post = for {
            ee <- evalExpr(pre.stack, e)
          } yield _sm_stack.modify(_ + (x -> ee))(pre)
          Process(post)
        case New(_, x, c) => Process(for {
          cdef <- defs.get(c).cata(_.right, s"Unknown class: $c".left)
          xsym = freshSym
          loc = freshLoc
          alloced =
              loc -> SpatialDesc(c, ExactDesc, cdef.children.mapValues(_ => SetLit(Seq())), cdef.refs.mapValues(_ => SetLit(Seq())))
        } yield (_sm_stack.modify(_ + (x -> SetLit(Seq(Symbol(xsym))))) andThen
                (_sm_heap ^|-> _sh_svltion).modify(_ + (Symbol(xsym) -> Loced(loc))) andThen
                (_sm_heap ^|-> _sh_locOwnership).modify(_ + (loc -> NewlyCreated)) andThen
                (_sm_heap ^|-> _sh_currentSpatial).modify(_ + alloced))(pre))
        case LoadField(_, x, e, f) => for {
          sym <- Process(evalExpr(pre.stack, e).flatMap(getSingletonSymbol))
          ares <- sym.traverse[TProcess, String, String \/ (SetExpr[IsSymbolic.type], SHeap)](s =>
                  access(s, f, pre.heap))(pmt).map(_.join)
        } yield ares.map { case (e, heap) => (_sm_stack.modify(_ + (x -> e)) andThen _sm_heap.set(heap))(pre)  }
        case AssignField(_, e1, f, e2) => {
          evalExpr(pre.stack, e1).flatMap(getSingletonSymbol).traverse[TProcess, String, String \/ SMem](sym =>
              evalExpr(pre.stack, e2).traverse[TProcess, String, String \/ SMem](ee2 =>
                    for {
                       newheaps <- update(sym, f, ee2, pre.heap)
                    } yield newheaps.map { case newheap => _sm_heap.set(newheap)(pre) }
              )(pmt).map(_.join)
          )(pmt).map(_.join)
        }
        case If(_, cond, ts, fs) => {
          val econdr = evalBoolExpr(pre.stack, cond)
          econdr traverseU { econd =>
            val newtmem = (_sm_heap ^|-> _sh_pure).modify(_ + econd)(pre)
            val newfmem = (_sm_heap ^|-> _sh_pure).modify(_ + not(econd))(pre)
            executeHelper(Process(newtmem), ts).interleave(executeHelper(Process(newfmem), fs))
          } map (_.join)
        }
        case For(_, x, m, sb) =>
          for {
            matchr <- (m match {
              case MSet(e) =>
                val ee = evalExpr(pre.stack, e)
                ee traverseU (e => modelFinder.findSet(e, pre.heap, beta)) map (_.join)
              case Match(e, c) =>
                val ee = evalExpr(pre.stack, e)
                ee traverseU (e => modelFinder.findSet(e, pre.heap, beta, targetClass = c.some)) map (_.join)
              case MatchStar(e, c) =>
                val ee = evalExpr(pre.stack, e)
                ???
            }) : Process[Task, String \/ (Set[Symbol], SHeap)]
            res <- matchr traverseU { case (syms : Set[Symbol], nheap) =>
                val nmem = _sm_heap.set(nheap)(pre)
                // TODO: Fix ordering so it coincides with concrete executor ordering
                syms.foldLeft(Process(nmem.right[String]) : Process[Task, String \/ SMem]) { (pmem, sym) =>
                  for {
                    memr <- pmem
                    res <- memr traverseU { mem =>
                      val nmem = _sm_stack.modify(_ + (x -> SetLit(Seq(sym))))
                      executeHelper(Process(mem), sb)
                    } map (_.join)
                  } yield res
                }
            } map (_.join)
          } yield res
        case Fix(_, e, sb) => {
          def fixEqCase(bmem: SMem): Process[Task, String \/ SMem] = {
            for {
              sbr <- executeHelper(Process(bmem), sb)
              res = for {
                  amem <- sbr
                  eeb <- evalExpr(bmem.stack, e)
                  eea <- evalExpr(amem.stack, e)
                } yield (_sm_heap ^|-> _sh_pure).modify(_ + Eq(eeb, eea))(amem)
            } yield res
          }
          def fixNeqCase(bmem: SMem, k: Int): Process[Task, String \/ SMem] = {
            for {
              sbr <- executeHelper(Process(bmem), sb)
              imemr = for {
                imem <- sbr
                eeb <- evalExpr(bmem.stack, e)
                eei <- evalExpr(imem.stack, e)
              } yield (_sm_heap ^|-> _sh_pure).modify(_ + Not(Eq(eeb, eei)))(imem)
              res <- imemr.traverse[TProcess, String, String \/ SMem]{ case imem =>
                if (k <= 0) fixEqCase(imem) else fixEqCase(imem) ++ fixNeqCase(imem, k - 1)
              }.map(_.join)
            } yield res
          }
          fixEqCase(pre) ++ fixNeqCase(pre, kappa)
        }
      }
    }
  }

  def evalBasicExpr(s: SStack, e: BasicExpr[IsProgram.type]): String \/ BasicExpr[IsSymbolic.type] = e match {
    case Var(name) =>
      s.get(name).cata({
            case SetLit(Seq(evalue)) => evalue.right
            case ee => s"Not a basic expression: $ee".left
        }, s"Error while evaluating expression $e".left)
  }

  def evalExpr(s : SStack, e : SetExpr[IsProgram.type]) : String \/ SetExpr[IsSymbolic.type] = {
      e match {
        case SetLit(es) =>
          for {
            ees <- es.toList.traverseU(e => evalBasicExpr(s, e))
          } yield SetLit(ees)
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

  def evalBoolExpr(st : SStack, sp : BoolExpr[IsProgram.type]) : String \/ BoolExpr[IsSymbolic.type] = sp match {
    case Eq(e1, e2) =>
      for {
        ee1 <- evalExpr(st, e1)
        ee2 <- evalExpr(st, e2)
      } yield Eq(ee1, ee2)
    case Not(p) =>
      for {
        ep <- evalBoolExpr(st, p)
      } yield Not(ep)
    case True() => True().right
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


  private val locCounter = Counter(0)

  private def freshLoc = Loc(locCounter.++)

  private val symCounter = Counter(0)

  private def freshSym: Symbols = symCounter.++

  val heapConsistencyChecker = new HeapConsistencyChecker(defs)

  val modelFinder = new ModelFinder(symCounter, locCounter, defs, beta, delta, optimistic = false)

  val typeInference = modelFinder.typeInference
}
