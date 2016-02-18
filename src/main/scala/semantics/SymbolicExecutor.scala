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
    Process0[String \/ (SetExpr[IsSymbolic.type], SHeap)] = (for {
      (loc, nheap) <- EitherT[Process0, String, (Loc, SHeap)](modelFinder.findLoc(sym, heap))
      (sdesc, nheap) <- EitherT[Process0, String, (SpatialDesc, SHeap)](modelFinder.unfold(loc, f, nheap))
      res <- EitherT[Process0, String, (SetExpr[IsSymbolic.type], SHeap)](if (defs.childfields.contains(f))
       (sdesc.children(f), nheap).right.point[Process0]
      else if (defs.reffields.contains(f))
        (sdesc.refs(f), nheap).right.point[Process0]
      else s"No value for field $f".left.point[Process0])
    } yield res).run

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

  def update(sym: Symbol, f: Fields, ee: SetExpr[IsSymbolic.type], heap: SHeap): Process0[String \/ SHeap] = (for {
      (loc, nheap) <- EitherT[Process0, String, (Loc, SHeap)](modelFinder.findLoc(sym, heap))
      (sdesc, nheap) <- EitherT[Process0, String, (SpatialDesc, SHeap)](modelFinder.unfold(loc, f, nheap))
      res <- EitherT[Process0, String, SHeap](if (defs.childfields.contains(f)) {
          val nnheap = disown(ee, loc, f, nheap)
          _sh_currentSpatial.modify(_.updated(loc, _sd_children.modify(_.updated(f, ee))(sdesc)))(nnheap).right.point[Process0]
        }
        else if (defs.reffields.contains(f))
          _sh_currentSpatial.modify(_.updated(loc, _sd_refs.modify(_.updated(f, ee))(sdesc)))(nheap).right.point[Process0]
        else s"No value for field $f".left.point[Process0])
    } yield res).run

  def execute(pres : Set[SMem], c : Statement): Process[Task, String \/ SMem] = {
     executeHelper(Process.emitAll(pres.toSeq), c)
  }

  private def executeHelper(pres : Process[Task, SMem], stmt : Statement) : Process[Task, String \/ SMem] = {
    // Todo parallelise using mergeN
    pres.flatMap[Task, String \/  SMem] { case (pre: SMem) =>
      if (!heapConsistencyChecker.isConsistent(pre.heap)) Process(s"Inconsistent memory ${PrettyPrinter.pretty(pre.heap)}".left)
      else stmt match {
        case StmtSeq(_,ss) => ss.toList.foldLeft(EitherT.right[TProcess, String, SMem](pre.point[TProcess])) { (memr, s) =>
          memr.flatMap { mem => EitherT[TProcess, String, SMem](executeHelper(Process(mem), s)) }
        }.run
        case AssignVar(_,x, e) =>
          val post = for {
            ee <- evalExpr(pre.stack, e)
          } yield _sm_stack.modify(_ + (x -> ee))(pre)
          Process(post)
        case New(_, x, c) =>
          val post = for {
            cdef <- defs.get(c).cata(_.right, s"Unknown class: $c".left)
            xsym = freshSym
            loc = freshLoc
            alloced =
                loc -> SpatialDesc(c, ExactDesc, cdef.children.mapValues(_ => SetLit(Seq())), cdef.refs.mapValues(_ => SetLit(Seq())), Map())
            updated =
              (_sm_stack.modify(_ + (x -> SetLit(Seq(Symbol(xsym))))) andThen
              (_sm_heap ^|-> _sh_svltion).modify(_ + (Symbol(xsym) -> Loced(loc))) andThen
              (_sm_heap ^|-> _sh_locOwnership).modify(_ + (loc -> NewlyCreated)) andThen
              (_sm_heap ^|-> _sh_currentSpatial).modify(_ + alloced))(pre)
          } yield updated
          Process(post)
        case LoadField(_, x, e, f) => (for {
          sym <- EitherT[TProcess, String, Symbol](evalExpr(pre.stack, e).flatMap(getSingletonSymbol).point[TProcess])
          (e, heap) <- EitherT[TProcess, String, (SetExpr[IsSymbolic.type], SHeap)](access(sym, f, pre.heap))
        } yield (_sm_stack.modify(_ + (x -> e)) andThen _sm_heap.set(heap))(pre)).run
        case AssignField(_, e1, f, e2) => (for {
            sym <- EitherT[TProcess, String, Symbol](evalExpr(pre.stack, e1).flatMap(getSingletonSymbol).point[TProcess])
            ee2 <- EitherT[TProcess, String, SetExpr[IsSymbolic.type]](evalExpr(pre.stack, e2).point[TProcess])
            newheap <- EitherT[TProcess, String, SHeap](update(sym, f, ee2, pre.heap))
          } yield _sm_heap.set(newheap)(pre)).run
        case If(_, cond, ts, fs) => (for {
          econd <- EitherT[TProcess, String, BoolExpr[IsSymbolic.type]](evalBoolExpr(pre.stack, cond).point[TProcess])
          newtmem = (_sm_heap ^|-> _sh_pure).modify(_ + econd)(pre)
          newfmem = (_sm_heap ^|-> _sh_pure).modify(_ + not(econd))(pre)
          res <-  EitherT[TProcess, String, SMem](executeHelper(Process(newtmem), ts).interleave(executeHelper(Process(newfmem), fs)))
        } yield res).run
        case For(_, x, m, sb) =>
          (for {
            (syms, nheap) <- m match {
              case MSet(e) =>
                for {
                  ee <- EitherT[TProcess, String, SetExpr[IsSymbolic.type]](evalExpr(pre.stack, e).point[TProcess])
                  set <- EitherT[TProcess, String, (Set[Symbol], SHeap)](modelFinder.findSet(ee, pre.heap, beta))
                } yield set
              case Match(e, c) =>
                for {
                  ee <- EitherT[TProcess, String, SetExpr[IsSymbolic.type]](evalExpr(pre.stack, e).point[TProcess])
                  set <- EitherT[TProcess, String, (Set[Symbol], SHeap)](modelFinder.findSet(ee, pre.heap, beta, targetClass = c.some))
                } yield set
              case MatchStar(e, c) =>
                for {
                  ee <- EitherT[TProcess, String, SetExpr[IsSymbolic.type]](evalExpr(pre.stack, e).point[TProcess])
                  set <- ??? : EitherT[TProcess, String, (Set[Symbol], SHeap)]
                } yield set
            }
            nmem = _sm_heap.set(nheap)(pre)

            // TODO: Fix ordering so it coincides with concrete executor ordering
            iterated <- syms.foldLeft(EitherT.right[TProcess, String, SMem](nmem.point[TProcess])) { (memr, sym) =>
              memr.flatMap { mem =>
                val nmem = _sm_stack.modify(_ + (x -> SetLit(Seq(sym))))(mem)
                EitherT[TProcess, String, SMem](executeHelper(Process(nmem), sb))
              }
            }
          } yield iterated).run
        case Fix(_, e, sb) => {
          def fixEqCase(bmem: SMem): Process[Task, String \/ SMem] = (for {
              amem <- EitherT[TProcess,String,SMem](executeHelper(Process(bmem), sb))
              eeb <- EitherT[TProcess,String,SetExpr[IsSymbolic.type]](evalExpr(bmem.stack, e).point[TProcess])
              eea <- EitherT[TProcess,String,SetExpr[IsSymbolic.type]](evalExpr(amem.stack, e).point[TProcess])
              updatedMem = (_sm_heap ^|-> _sh_pure).modify(_ + Eq(eeb, eea))(amem)
            } yield updatedMem).run
          def fixNeqCase(bmem: SMem, k: Int): Process[Task, String \/ SMem] = (for {
              imem <- EitherT[TProcess,String,SMem](executeHelper(Process(bmem), sb))
              eeb <- EitherT[TProcess,String,SetExpr[IsSymbolic.type]](evalExpr(bmem.stack, e).point[TProcess])
              eei <- EitherT[TProcess,String,SetExpr[IsSymbolic.type]](evalExpr(imem.stack, e).point[TProcess])
              updatedMem = (_sm_heap ^|-> _sh_pure).modify(_ + Not(Eq(eeb, eei)))(imem)
              res <- EitherT[TProcess,String,SMem](if (k <= 0) fixEqCase(imem) else fixEqCase(imem) ++ fixNeqCase(imem, k - 1))
            } yield res).run
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
    case True() => True[IsSymbolic.type]().right
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
