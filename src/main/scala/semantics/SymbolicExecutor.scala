package semantics

import helper._
import semantics.domains.SHeap._
import semantics.domains.SMem._
import semantics.domains.SpatialDesc._
import semantics.domains._
import syntax.ast._

import scala.language.higherKinds
import scalaz.Scalaz._
import scalaz._
import scalaz.concurrent.Task
import scalaz.stream._

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
    EitherT[TProcess, String, (SetExpr[IsSymbolic.type], SHeap)] = for {
      (loc, nheap) <- EitherT[TProcess, String, (Loc, SHeap)](modelFinder.findLoc(sym, heap))
      _ = println(s"access-loc: $loc, heap: $nheap")
      (sdesc, nnheap) <- EitherT[TProcess, String, (SpatialDesc, SHeap)](modelFinder.unfold(loc, f, nheap))
      _ = println(s"access-sdesc: $sdesc, heap: $nnheap")
      res <- EitherT[TProcess, String, (SetExpr[IsSymbolic.type], SHeap)](if (defs.childfields.contains(f))
       (sdesc.children(f), nnheap).right.point[TProcess]
      else if (defs.reffields.contains(f))
        (sdesc.refs(f), nnheap).right.point[TProcess]
      else s"No value for field $f".left.point[TProcess])
    } yield res

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

  def update(sym: Symbol, f: Fields, ee: SetExpr[IsSymbolic.type], heap: SHeap): EitherT[TProcess, String, SHeap] = for {
      (loc, nheap) <- EitherT[TProcess, String, (Loc, SHeap)](modelFinder.findLoc(sym, heap))
      (sdesc, nheap) <- EitherT[TProcess, String, (SpatialDesc, SHeap)](modelFinder.unfold(loc, f, nheap))
      res <- EitherT[TProcess, String, SHeap](if (defs.childfields.contains(f)) {
          val nnheap = disown(ee, loc, f, nheap)
          _sh_currentSpatial.modify(_.updated(loc, _sd_children.modify(_.updated(f, ee))(sdesc)))(nnheap).right.point[Process0]
        }
        else if (defs.reffields.contains(f))
          _sh_currentSpatial.modify(_.updated(loc, _sd_refs.modify(_.updated(f, ee))(sdesc)))(nheap).right.point[Process0]
        else s"No value for field $f".left.point[Process0])
    } yield res

  def execute(pres : Set[SMem], c : Statement): Process[Task, String \/ SMem] = {
     executeHelper(Process.emitAll(pres.toSeq), c).run
  }

  private def executeHelper(pres : Process[Task, SMem], stmt : Statement) : EitherT[TProcess, String, SMem] = {
    // Todo parallelise using mergeN
    EitherT.right[TProcess, String, SMem](pres).flatMap { case (pre: SMem) =>
      val concretised = modelFinder.concretise(pre)
      println(s"pre: ${pre.heap.initSpatial}")
      println(s"concretised: $concretised")
      if (!concretised.isRight) EitherT.left[TProcess, String, SMem](s"Inconsistent memory ${PrettyPrinter.pretty(pre)}".point[TProcess])
      else stmt match {
        case StmtSeq(_,ss) => ss.toList.foldLeft(EitherT.right[TProcess, String, SMem](pre.point[TProcess])) { (memr, s) =>
          memr.flatMap { mem => executeHelper(Process(mem), s) }
        }
        case AssignVar(_,x, e) => for {
            ee <- evalExpr[TProcess](pre.currentStack, e)
          } yield _sm_currentStack.modify(_ + (x -> ee))(pre)
        case New(_, x, c) =>
          val post = for {
            cdef <- defs.get(c).cata(_.right, s"Unknown class: $c".left)
            xsym = freshSym
            loc = freshLoc
            alloced =
                loc -> SpatialDesc(c, ExactDesc, cdef.children.mapValues(_ => SetLit(Seq())), cdef.refs.mapValues(_ => SetLit(Seq())), Map())
            updated =
              (_sm_currentStack.modify(_ + (x -> SetLit(Seq(Symbol(xsym))))) andThen
              (_sm_heap ^|-> _sh_svltion).modify(_ + (Symbol(xsym) -> Loced(loc))) andThen
              (_sm_heap ^|-> _sh_locOwnership).modify(_ + (loc -> NewlyCreated)) andThen
              (_sm_heap ^|-> _sh_currentSpatial).modify(_ + alloced))(pre)
          } yield updated
          EitherT[TProcess, String, SMem](post.point[TProcess])
        case LoadField(_, x, e, f) => for {
          sym <- evalExpr[TProcess](pre.currentStack, e).flatMap(getSingletonSymbol[TProcess])
          (e, heap) <- access(sym, f, pre.heap)
        } yield (_sm_currentStack.modify(_ + (x -> e)) andThen _sm_heap.set(heap))(pre)
        case AssignField(_, e1, f, e2) => for {
            sym <- evalExpr[TProcess](pre.currentStack, e1).flatMap(getSingletonSymbol[TProcess])
            ee2 <- evalExpr[TProcess](pre.currentStack, e2)
            newheap <- update(sym, f, ee2, pre.heap)
          } yield _sm_heap.set(newheap)(pre)
        case If(_, cond, ts, fs) => for {
          econd <- evalBoolExpr[TProcess](pre.currentStack, cond)
          newtmem = (_sm_heap ^|-> _sh_pure).modify(_ + econd)(pre)
          newfmem = (_sm_heap ^|-> _sh_pure).modify(_ + not(econd))(pre)
          // TODO rewrite using liftA2?
          res <-  EitherT[TProcess, String, SMem](executeHelper(Process(newtmem), ts).run.interleave(executeHelper(Process(newfmem), fs).run))
        } yield res
        case For(_, x, m, sb) =>
          for {
            (syms, imem) <- m match {
              case MSet(e) =>
                for {
                  ee <- evalExpr[TProcess](pre.currentStack, e)
                  set <- EitherT[TProcess, String, (Set[Symbol], SMem)](modelFinder.findSet(ee, pre, beta))
                } yield set
              case Match(e, c) =>
                for {
                  ee <- evalExpr[TProcess](pre.currentStack, e)
                  set <- EitherT[TProcess, String, (Set[Symbol], SMem)](modelFinder.findSet(ee, pre, beta, targetClass = c.some))
                } yield set
              case MatchStar(e, c) =>
                for {
                  ee <- evalExpr[TProcess](pre.currentStack, e)
                  set <- EitherT[TProcess, String, (Set[Symbol], SMem)](modelFinder.findSet(ee, pre, beta))
                } yield set
            }
            // TODO: Fix ordering so it coincides with concrete executor ordering
            iterated <- syms.foldLeft(EitherT.right[TProcess, String, SMem](imem.point[TProcess])) { (memr, sym) =>
              memr.flatMap { mem => executeHelper(Process(_sm_currentStack.modify(_ + (x -> SetLit(Seq(sym))))(mem)), sb) }
            }
          } yield iterated
        case Fix(_, e, sb) => {
          def fixEqCase(bmem: SMem): EitherT[TProcess, String, SMem] = for {
              amem <- executeHelper(Process(bmem), sb)
              eeb <- evalExpr[TProcess](bmem.currentStack, e)
              eea <- evalExpr[TProcess](amem.currentStack, e)
              updatedMem = (_sm_heap ^|-> _sh_pure).modify(_ + Eq(eeb, eea))(amem)
            } yield updatedMem
          def fixNeqCase(bmem: SMem, k: Int): EitherT[TProcess, String, SMem] = for {
              imem <- executeHelper(Process(bmem), sb)
              eeb <- evalExpr[TProcess](bmem.currentStack, e)
              eei <- evalExpr[TProcess](imem.currentStack, e)
              updatedMem = (_sm_heap ^|-> _sh_pure).modify(_ + Not(Eq(eeb, eei)))(imem)
              fixmore <- if (k <= 0) fixEqCase(imem) else EitherT[TProcess,String,SMem](fixEqCase(imem).run ++ fixNeqCase(imem, k - 1).run)
            } yield fixmore
          EitherT[TProcess,String,SMem](fixEqCase(pre).run ++ fixNeqCase(pre, kappa).run)
        }
      }
    }
  }

  def evalBasicExpr[M[_] : Monad](s: SStack, e: BasicExpr[IsProgram.type]): EitherT[M, String, BasicExpr[IsSymbolic.type]] = e match {
    case Var(name) =>
      s.get(name).cata({
            case SetLit(Seq(evalue)) => EitherT.right(evalue.point[M])
            case ee => EitherT.left(s"Not a basic expression: $ee".point[M])
        }, EitherT.left(s"Error while evaluating expression $e".point[M]))
  }

  def evalExpr[M[_] : Monad](s : SStack, e : SetExpr[IsProgram.type]) : EitherT[M, String, SetExpr[IsSymbolic.type]] = {
      e match {
        case SetLit(es) =>
          for {
            ees <- es.toList.traverseU(e => evalBasicExpr[M](s, e))
          } yield SetLit(ees)
        case SetVar(name) =>
          EitherT(s.get(name).cata(_.right, s"Error whie evaluating expression $e".left).point[M])
        case Diff(e1, e2) => for {
          ee1 <- evalExpr[M](s, e1)
          ee2 <- evalExpr[M](s, e2)
        } yield Diff(ee1, ee2)
        case Union(e1, e2) => for {
          ee1 <- evalExpr[M](s, e1)
          ee2 <- evalExpr[M](s, e2)
        } yield Union(ee1, ee2)
        case ISect(e1, e2) => for {
          ee1 <- evalExpr[M](s, e1)
          ee2 <- evalExpr[M](s, e2)
        } yield ISect(ee1, ee2)
      }
    }

  def evalBoolExpr[M[_] : Monad](st : SStack, sp : BoolExpr[IsProgram.type]) : EitherT[M, String, BoolExpr[IsSymbolic.type]] = sp match {
    case Eq(e1, e2) =>
      for {
        ee1 <- evalExpr[M](st, e1)
        ee2 <- evalExpr[M](st, e2)
      } yield Eq(ee1, ee2)
    case Not(p) =>
      for {
        ep <- evalBoolExpr[M](st, p)
      } yield Not(ep)
    case True() => EitherT.right((True() : BoolExpr[IsSymbolic.type]).point[M])
    case And(p1, p2) =>
      for {
        ep1 <- evalBoolExpr[M](st, p1)
        ep2 <- evalBoolExpr[M](st, p2)
      } yield And(ep1, ep2)
    case SetMem(e1, e2) =>
      for {
        ee1 <- evalBasicExpr[M](st, e1)
        ee2 <- evalExpr[M](st, e2)
      } yield SetMem(ee1, ee2)
    case SetSubEq(e1, e2) =>
      for {
        ee1 <- evalExpr[M](st, e1)
        ee2 <- evalExpr[M](st, e2)
      } yield SetSubEq(ee1, ee2)
  }


  private val locCounter = Counter(0)

  private def freshLoc = Loc(locCounter.++)

  private val symCounter = Counter(0)

  private def freshSym: Symbols = symCounter.++

  val modelFinder = new ModelFinder(symCounter, locCounter, defs, beta, delta, optimistic = false)

  val typeInference = modelFinder.typeInference
}
