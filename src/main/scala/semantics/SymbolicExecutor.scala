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
    EitherT[List, String, (SetExpr[IsSymbolic.type], SHeap)] =
    {
      val res = for {
        (loc, nheap) <- EitherT[List, String, (Loc, SHeap)](modelFinder.findLoc(sym, heap).toList)
        (sdesc, nnheap) <- EitherT[List, String, (SpatialDesc, SHeap)](modelFinder.unfold(loc, f, nheap).toList)
        res <- EitherT[List, String, (SetExpr[IsSymbolic.type], SHeap)](if (defs.childfields.contains(f))
          (sdesc.children(f), nnheap).right.point[List]
        else if (defs.reffields.contains(f))
          (sdesc.refs(f), nnheap).right.point[List]
        else s"No value for field $f".left.point[List])
      } yield res
      res
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
    EitherT[TProcess, String, SMem](pres.map(_.right)).flatMap { (pre: SMem) =>
      val concretised = modelFinder.concretise(pre)
      if (!concretised.isRight) {
        EitherT[TProcess, String, SMem](s"Inconsistent memory ${PrettyPrinter.pretty(pre)}".left.point[TProcess])
      } else stmt match {
        case StmtSeq(_,ss) => ss.toList.foldLeft(EitherT[TProcess, String, SMem](pre.right.point[TProcess])) { (memr, s) =>
          memr.flatMap { mem =>
            executeHelper(Process(mem), s)
          }
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
          eres <- evalExpr[TProcess](pre.currentStack, e)
          (sym, mem) <- findSym(pre, eres)
          (e, nheap) <- EitherT[TProcess, String, (SetExpr[IsSymbolic.type], SHeap)](Process.emitAll(access(sym, f, mem.heap).run))
        } yield (_sm_currentStack.modify(_ + (x -> e)) andThen _sm_heap.set(nheap))(pre)
        case AssignField(_, e1, f, e2) => for {
            e1res <- evalExpr[TProcess](pre.currentStack, e1)
            (sym, mem) <- findSym(pre, e1res)
            ee2 <- evalExpr[TProcess](pre.currentStack, e2)
            nheap <- update(sym, f, ee2, mem.heap)
          } yield _sm_heap.set(nheap)(pre)
        case If(_, cond, ts, fs) => for {
          econd <- evalBoolExpr[TProcess](pre.currentStack, cond)
          newtmem = (_sm_heap ^|-> _sh_pure).modify(_ + econd)(pre)
          newfmem = (_sm_heap ^|-> _sh_pure).modify(_ + not(econd))(pre)
          // TODO rewrite using liftA2?
          execTrue = executeHelper(Process(newtmem), ts).run
          execFalse = executeHelper(Process(newfmem), fs).run
          res <-  EitherT[TProcess, String, SMem](execTrue.tee(execFalse)(teePlus.interleaveAll))
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
            iterated <- syms.foldLeft(EitherT[TProcess, String, SMem](imem.right.point[TProcess])) { (memr, sym) =>
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

  private def findSym(mem: SMem, eres: SetExpr[IsSymbolic.type]): DisjunctionT[TProcess, String, (Symbol, SMem)] = {
    eres match {
      case SetLit(Seq(s: Symbol)) => EitherT[TProcess, String, (Symbol, SMem)]((s, mem).right.point[TProcess])
      case ee => {
        val nsym = Symbol(freshSym)
        val nsymownership = SUnowned// TODO: Pick proper ownership
        for {
          nsymtype <- EitherT[TProcess, String, Class](typeInference.inferSetType(ee, mem.heap).cata(_.right.point[TProcess], s"Empty set $eres".left.point[TProcess]))
          nmem = ((_sm_heap ^|-> _sh_svltion).modify(_ + (nsym -> UnknownLoc(nsymtype, nsymownership, Map()))) andThen
                      (_sm_heap ^|-> _sh_pure).modify(_ + Eq(SetLit(Seq(nsym)), ee)))(mem)
          concretise <- EitherT[TProcess, String, CMem](modelFinder.concretise(nmem).point[TProcess])
        } yield (nsym, nmem)
      }
    }
  }

  def evalBasicExpr[M[_] : Monad](s: SStack, e: BasicExpr[IsProgram.type]): EitherT[M, String, BasicExpr[IsSymbolic.type]] = e match {
    case Var(name) =>
      s.get(name).cata({
            case SetLit(Seq(evalue)) => EitherT(evalue.right.point[M])
            case ee => EitherT(s"Not a basic expression: $ee".left.point[M])
        }, EitherT(s"Error while evaluating expression $e".left.point[M]))
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
    case True() => EitherT((True() : BoolExpr[IsSymbolic.type]).right.point[M])
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
