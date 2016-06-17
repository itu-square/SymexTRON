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
import MatchExpr._
import org.scalatest.tools.ReporterConfigurations

class SymbolicExecutor(defs: Map[Class, ClassDefinition],
                       kappa: Int = 3, delta: Int = 3, beta: Int = 5) {

  //TODO Implement clean up function of heap, that removes unneeded constraints

  def access(sym: Symbol, f: Fields, heap: SHeap):
    EitherT[Process[Task, ?], String, (SetExpr[IsSymbolic.type], SHeap)] =
    {
      for {
        (Seq(loc), nheap) <- EitherT[Process[Task, ?], String, (Seq[Loc], SHeap)](lazyInitializer.findLocs(Seq(sym), heap))
        (sdesc, nnheap) <- EitherT[Process[Task, ?], String, (SpatialDesc, SHeap)](lazyInitializer.unfold(loc, f, nheap))
        res <- EitherT[Process[Task, ?], String, (SetExpr[IsSymbolic.type], SHeap)](if (defs.childfields.contains(f))
          (sdesc.children(f), nnheap).right.point[Process[Task, ?]]
        else if (defs.reffields.contains(f))
          (sdesc.refs(f), nnheap).right.point[Process[Task, ?]]
        else s"No value for field $f".left.point[Process[Task, ?]])
      } yield res
    }

  // TODO Handle descendant constraints as well
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

  def update(sym: Symbol, f: Fields, ee: SetExpr[IsSymbolic.type], heap: SHeap): EitherT[Process[Task, ?], String, SHeap] = for {
      (Seq(loc), nheap) <- EitherT[Process[Task, ?], String, (Seq[Loc], SHeap)](lazyInitializer.findLocs(Seq(sym), heap))
      (sdesc, nnheap) <- EitherT[Process[Task, ?], String, (SpatialDesc, SHeap)](lazyInitializer.unfold(loc, f, nheap))
      res <- EitherT[Process[Task, ?], String, SHeap](if (defs.childfields.contains(f)) {
          val nnnheap = disown(ee, loc, f, nnheap)
          _sh_currentSpatial.modify(_.updated(loc, _sd_children.modify(_.updated(f, ee))(sdesc)))(nnnheap).right.point[Process0]
        }
        else if (defs.reffields.contains(f))
          _sh_currentSpatial.modify(_.updated(loc, _sd_refs.modify(_.updated(f, ee))(sdesc)))(nnheap).right.point[Process0]
        else s"No value for field $f".left.point[Process0])
    } yield res

  def execute(pres : Set[SMem], c : Statement): Process[Task, String \/ SMem] = {
    for {
      pre <- Process.emitAll(pres.toSeq)
      _ <- checkMemoryConsistency(pre).point[Process[Task, ?]]
      res <- executeHelper(pre, c).run
    } yield res
  }


  def checkMemoryConsistency(pre: SMem): Process[Task, String \/ CMem] = {
    val concretised = modelFinder.concretise(pre)
    concretised.point[Process[Task,?]].map(_.leftMap(err => { s"Inconsistent memory: ${PrettyPrinter.pretty(pre, initial = true)}" }))
  }

  def matchLocs(locs: Seq[Loc], c: Class, mem: SMem): String \/ (SetExpr[IsSymbolic.type], SMem) = {
    def addDescendantPool(descendantpools: DescendantPools, c: Class) = {
      if (descendantpools.contains(c)) (descendantpools(c), descendantpools, Map[SetSymbol, SSymbolDesc](), Set[BoolExpr[IsSymbolic.type]]())
      else {
        // TODO optimize if can't contain things of that type
        val ssym = SetSymbol(freshSym)
        val superdps = defs.supertypes(c).map(descendantpools.get).filter(_.isDefined).map(_.get)
        val subdps = defs.subtypes(c).map(descendantpools.get).filter(_.isDefined).map(_.get)
        val constraints = superdps.map(superssym => SetSubEq(ssym, superssym)).toSet[BoolExpr[IsSymbolic.type]] ++
                             subdps.map(subssym => SetSubEq(subssym, ssym)).toSet[BoolExpr[IsSymbolic.type]]
        (ssym, descendantpools + (c -> ssym), Map(ssym -> SSymbolDesc(c, ManyOpt)), constraints)
      }
    }
    locs.foldLeft((Seq[SetExpr[IsSymbolic.type]](), mem).right[String]) { (st, loc) =>
      for {
        (presyms, mem) <- st
        sdesc = mem.heap.currentSpatial(loc)
        (ssym, newdp, newsslvtion, newpure) = addDescendantPool(sdesc.descendantpools, c)
      } yield (presyms :+ ssym,
            ((_sm_heap ^|-> _sh_ssvltion).modify(_ ++ newsslvtion) andThen
              (_sm_heap ^|-> _sh_initSpatial).modify(_ + (loc -> _sd_descendantpools.set(newdp)(sdesc))) andThen
                (_sm_heap ^|-> _sh_currentSpatial).modify(_ + (loc -> _sd_descendantpools.set(newdp)(sdesc))) andThen
                  (_sm_heap ^|-> _sh_pure).modify(_ ++ newpure))(mem))
    }.map { case (ssyms, mem) =>
      if (ssyms.isEmpty) (SetLit(Seq()), mem) else {
      val ssymdisjoint : Seq[BoolExpr[IsSymbolic.type]] =
        for (ssym1 <- ssyms; ssym2 <- ssyms; if ssym1 != ssym2) yield Eq(Union(ssym1, ssym2), SetLit(Seq()))
      (ssyms.tail.foldLeft(ssyms.head : SetExpr[IsSymbolic.type])(Union(_,_)),
        (_sm_heap ^|-> _sh_pure).modify(_ ++ ssymdisjoint.toSet)(mem))
      }
    }
  }



  private def executeHelper(pre : SMem, stmt : Statement) : EitherT[Process[Task, ?], String, SMem] = {
    // TODO parallelise using mergeN
    stmt match {
      case StmtSeq(_,ss) => ss.toList.foldLeft(EitherT[Process[Task, ?], String, SMem](pre.right.point[Process[Task, ?]])) { (memr, s) =>
        memr.flatMap { mem => executeHelper(mem, s) }
      }
      case AssignVar(_,x, e) => for {
          ee <- evalSetExpr[Process[Task, ?]](_sm_currentStack.get(pre), e)
        } yield _sm_currentStack.modify(_ + (x -> ee))(pre)
      case New(_, x, c) =>
        val post = for {
          cdef <- defs.get(c).cata(_.right, s"Unknown class: $c".left)
          xsym = freshSym
          loc = freshLoc
          alloced =
              loc -> SpatialDesc(c, Set(), ExactDesc, defs.childrenOf(defs.supertypes(c) + c).mapValues(_ => SetLit(Seq())), defs.refsOf(defs.supertypes(c) + c).mapValues(_ => SetLit(Seq())), Map())
          updated =
            (_sm_currentStack.modify(_ + (x -> SetLit(Seq(Symbol(xsym))))) andThen
            (_sm_heap ^|-> _sh_svltion).modify(_ + (Symbol(xsym) -> Loced(loc))) andThen
            (_sm_heap ^|-> _sh_locOwnership).modify(_ + (loc -> NewlyCreated)) andThen
            (_sm_heap ^|-> _sh_currentSpatial).modify(_ + alloced))(pre)
        } yield updated
        EitherT[Process[Task, ?], String, SMem](post.point[Process[Task, ?]])
      case LoadField(_, x, e, f) => for {
        eres <- evalSetExpr[Process[Task, ?]](_sm_currentStack.get(pre), e)
        (Seq(sym), _, mem) <- EitherT[Process[Task, ?], String, (Seq[Symbol], SetExpr[IsSymbolic.type], SMem)](findSyms(1, pre, eres).point[Process[Task, ?]])
        (e, nheap) <- access(sym, f, mem.heap)
      } yield (_sm_currentStack.modify(_ + (x -> e)) andThen _sm_heap.set(nheap))(mem)
      case AssignField(_, e1, f, e2) => for {
          e1res <- evalSetExpr[Process[Task, ?]](_sm_currentStack.get(pre), e1)
          (Seq(sym), _, mem) <- EitherT[Process[Task, ?], String, (Seq[Symbol], SetExpr[IsSymbolic.type], SMem)](findSyms(1, pre, e1res).point[Process[Task, ?]])
          ee2 <- evalSetExpr[Process[Task, ?]](_sm_currentStack.get(mem), e2)
          nheap <- update(sym, f, ee2, mem.heap)
        } yield _sm_heap.set(nheap)(mem)
      case If(_, cond, ts, fs) => for {
        econd <- evalBoolExpr[Process[Task, ?]](_sm_currentStack.get(pre), cond)
        newtmem = (_sm_heap ^|-> _sh_pure).modify(_ + econd)(pre)
        newfmem = (_sm_heap ^|-> _sh_pure).modify(_ + not(econd))(pre)
        execTrue =
          for {
            _ <- EitherT[Process[Task, ?], String, CMem](checkMemoryConsistency(newtmem))
            res <- executeHelper(newtmem, ts)
          } yield res
        execFalse =
          for {
            _ <- EitherT[Process[Task, ?], String, CMem](checkMemoryConsistency(newfmem))
            res <- executeHelper(newfmem, fs)
          } yield res
        res <-  EitherT[Process[Task, ?], String, SMem](execTrue.run.tee(execFalse.run)(teePlus.interleaveAll))
      } yield res
      case For(_, x, m, sb) =>
        for {
          ee <- evalSetExpr[Process[Task, ?]](_sm_currentStack.get(pre), _me_e.get(m))
          (syms, oee, imem) <-  EitherT[Process[Task, ?], String, (Seq[Symbol], SetExpr[IsSymbolic.type], SMem)](Process.emitAll(List.range(0,beta + 1)).map {
            count => findSyms(count, pre, ee)
          })
          (nsyms, nimem) <- m match {
            case MSet(e) => EitherT.right[Process[Task, ?], String, (Seq[Symbol], SMem)]((syms, imem).point[Process[Task, ?]])
            case Match(e, c) =>
                EitherT.right[Process[Task, ?], String, (Seq[Symbol], Seq[Symbol], SMem)](Process.emitAll(matchSyms(oee, syms, imem, c))).map { case (incsyms, _, mem) => (incsyms, mem) }
            case MatchStar(e, c) =>
              for {
                (incsyms, excsyms, nimem) <- EitherT.right[Process[Task, ?], String, (Seq[Symbol], Seq[Symbol], SMem)](Process.emitAll(matchSyms(oee, syms, imem, c)))
                (locs, nniheap) <- EitherT[Process[Task, ?], String, (Seq[Loc], SHeap)](lazyInitializer.findLocs(incsyms ++ excsyms, nimem.heap))
                nnmem = _sm_heap.set(nniheap)(nimem)
                (dpe, fmem) <- EitherT[Process[Task, ?], String, (SetExpr[IsSymbolic.type], SMem)](matchLocs(locs, c, nnmem).point[Process[Task, ?]])
                (msyms, _, nfmem) <- EitherT[Process[Task, ?], String, (Seq[Symbol], SetExpr[IsSymbolic.type], SMem)](Process.emitAll(List.range(0,beta + 1 - incsyms.length)).map {
                  count => findSyms(count, fmem, dpe)
                })
              } yield (incsyms ++ msyms, nfmem)
          }
          _ <- EitherT[Process[Task, ?], String, CMem](checkMemoryConsistency(nimem))
          // TODO: Fix ordering so it coincides with concrete executor ordering
          iterated <- nsyms.foldLeft(EitherT[Process[Task, ?], String, SMem](nimem.right.point[Process[Task, ?]])) { (memr, sym) =>
            memr.flatMap { mem => executeHelper(_sm_currentStack.modify(_ + (x -> SetLit(Seq(sym))))(mem), sb) }
          }
        } yield iterated
      case Fix(_, e, sb) =>
        def fixEqCase(bmem: SMem): EitherT[Process[Task, ?], String, SMem] = for {
            _ <- EitherT[Process[Task, ?], String, CMem](checkMemoryConsistency(bmem))
            amem <- executeHelper(bmem, sb)
            eeb <- evalSetExpr[Process[Task, ?]](_sm_currentStack.get(bmem), e)
            eea <- evalSetExpr[Process[Task, ?]](_sm_currentStack.get(amem), e)
            updatedMem = (_sm_heap ^|-> _sh_pure).modify(_ + Eq(eeb, eea))(amem)
          } yield updatedMem
        def fixNeqCase(bmem: SMem, k: Int): EitherT[Process[Task, ?], String, SMem] = for {
            _ <- EitherT[Process[Task, ?], String, CMem](checkMemoryConsistency(bmem))
            imem <- executeHelper(bmem, sb)
            eeb <- evalSetExpr[Process[Task, ?]](_sm_currentStack.get(bmem), e)
            eei <- evalSetExpr[Process[Task, ?]](_sm_currentStack.get(imem), e)
            updatedMem = (_sm_heap ^|-> _sh_pure).modify(_ + Not(Eq(eeb, eei)))(imem)
            fixmore <- if (k <= 0) fixEqCase(imem) else EitherT[Process[Task, ?],String,SMem](fixEqCase(imem).run ++ fixNeqCase(imem, k - 1).run)
          } yield fixmore
        EitherT[Process[Task, ?],String,SMem](fixEqCase(pre).run ++ fixNeqCase(pre, kappa).run)
    }
  }


  def matchSyms(ee: SetExpr[IsSymbolic.type], syms: Seq[Symbol], imem: SMem, c: Class): Seq[(Seq[Symbol], Seq[Symbol], SMem)] = {
    def partitionSyms(syms: Seq[Symbol], mem: SMem, c: Class): Seq[(Seq[Symbol], Seq[Symbol], SMem)] = for {
      (incl, excl) <- List.range(0, syms.length + 1).map(syms.splitAt)
      nmem = (_sm_heap ^|-> _sh_svltion).modify(_.mapValuesWithKeys((s, sdesc) =>
        sdesc match {
          case Loced(l) => sdesc // TODO Refine loc with type?
          case sdesc:UnknownLoc =>
            if (excl.contains(s)) { sdesc.copy(notinstof = sdesc.notinstof + c) }
            else if (incl.contains(s)) { sdesc.copy(cl = c, notinstof = sdesc.notinstof.intersect(defs.subtypesOrSelf(c))) }
            else sdesc
        }
      ))(mem)
    } yield (incl, excl, nmem)
    val ocr = typeInference.inferSetType(ee, imem.heap)
    ocr.cata({ oc =>
      if (defs.subtypesOrSelf(c).contains(oc)) Seq((syms, Seq(), imem))
      else if (defs.maxClass(c, oc).isDefined) partitionSyms(syms, imem, c)
      else Seq((Seq(), syms, imem))
    }, Seq((Seq(), syms, imem)))
  }

  private def partition1(mem: SMem, eres: SetExpr[IsSymbolic.type]): String \/ (Symbol, SetExpr[IsSymbolic.type], SMem) = eres match {
    case SetLit(es) =>
      es match {
        case Seq() => s"Empty set: $eres".left
        case x@Symbol(_) +: xs => (x, SetLit(xs) : SetExpr[IsSymbolic.type], mem).right[String]
      }
    case _ =>
      val nsym = Symbol(freshSym)
      val nssym = SetSymbol(freshSym)
      for {
        nsymtype <- typeInference.inferSetType(eres, mem.heap).cata(_.right, s"Empty set: $eres".left)
        nmem = ((_sm_heap ^|-> _sh_svltion).modify(_.updated(nsym, UnknownLoc(nsymtype, Set()))) andThen
                (_sm_heap ^|-> _sh_ssvltion).modify(_.updated(nssym, SSymbolDesc(nsymtype, ManyOpt))) andThen
                (_sm_heap ^|-> _sh_pure).modify(_ + Eq(ISect(SetLit(Seq(nsym)), nssym), SetLit(Seq())) + Eq(Union(SetLit(Seq(nsym)), nssym), eres)))(mem)
      } yield (nsym, nssym, nmem)
  }

  private def findSyms(count: Int, mem: SMem, eres: SetExpr[IsSymbolic.type]): String \/ (Seq[Symbol], SetExpr[IsSymbolic.type], SMem) = {
    def cardMatches(crd: Cardinality, count: Symbols) = crd match {
      case ManyReq => 1 <= count
      case Req => count == 1
      case ManyOpt => true
      case Opt => count <= 1
    }
    eres match {
      case SetLit(syms) =>
        if (syms.length == count) (syms.map {case s:Symbol => s}, eres, mem).right[String]
        else s"Mismatch between count of ${PrettyPrinter.pretty(eres)} and needed count $count".left
      case ee =>
        val nsyms = Seq.fill(count)(Symbol(freshSym))
        for {
          nsymtype <- typeInference.inferSetType(ee, mem.heap).cata(_.right, s"Empty set $eres".left)
          nmem = ((_sm_heap ^|-> _sh_svltion).modify(_ ++ nsyms.map(_ -> UnknownLoc(nsymtype, Set()))) andThen
                      (_sm_heap ^|-> _sh_pure).modify(_ + Eq(SetLit(nsyms), ee)))(mem)
          concretise <- modelFinder.concretise(nmem)
        } yield (nsyms, eres, nmem)
    }
  }

  def evalSetExpr[M[_] : Monad](s : SStackState, e : SetExpr[IsProgram.type]) : EitherT[M, String, SetExpr[IsSymbolic.type]] = {
      e match {
        case SetLit(es) =>
          assert (es.isEmpty)
          EitherT.right[M, String, SetExpr[IsSymbolic.type]]((SetLit(Seq()) : SetExpr[IsSymbolic.type]).point[M])
        case Var(name) =>
          EitherT(s.get(name).cata(_.right, s"Error while evaluating expression $e".left).point[M])
        case Diff(e1, e2) => for {
          ee1 <- evalSetExpr[M](s, e1)
          ee2 <- evalSetExpr[M](s, e2)
        } yield Diff(ee1, ee2)
        case Union(e1, e2) => for {
          ee1 <- evalSetExpr[M](s, e1)
          ee2 <- evalSetExpr[M](s, e2)
        } yield Union(ee1, ee2)
        case ISect(e1, e2) => for {
          ee1 <- evalSetExpr[M](s, e1)
          ee2 <- evalSetExpr[M](s, e2)
        } yield ISect(ee1, ee2)
      }
    }

  def evalBoolExpr[M[_] : Monad](st : SStackState, sp : BoolExpr[IsProgram.type]) : EitherT[M, String, BoolExpr[IsSymbolic.type]] = sp match {
    case Eq(e1, e2) =>
      for {
        ee1 <- evalSetExpr[M](st, e1)
        ee2 <- evalSetExpr[M](st, e2)
      } yield Eq(ee1, ee2)
    case Not(p) =>
      for {
        ep <- evalBoolExpr[M](st, p)
      } yield Not(ep)
    case True() => EitherT((True() : BoolExpr[IsSymbolic.type]).right[String].point[M])
    case And(p1, p2) =>
      for {
        ep1 <- evalBoolExpr[M](st, p1)
        ep2 <- evalBoolExpr[M](st, p2)
      } yield And(ep1, ep2)
    case SetSubEq(e1, e2) =>
      for {
        ee1 <- evalSetExpr[M](st, e1)
        ee2 <- evalSetExpr[M](st, e2)
      } yield SetSubEq(ee1, ee2)
    case BagSubEquiv(_, e1, e2) =>
      for {
        ee1 <- evalSetExpr[M](st, e1)
        ee2 <- evalSetExpr[M](st, e2)
      } yield BagSubEquiv[Option[Any], IsSymbolic.type](None, ee1, ee2)
  }


  private val locCounter = Counter(0)

  private def freshLoc = Loc(locCounter.++)

  private val symCounter = Counter(0)

  private def freshSym: Symbols = symCounter.++

  val lazyInitializer = new LazyInitializer(symCounter, locCounter, defs, optimistic = false)

  val modelFinder = new ModelFinder(defs, delta)

  val typeInference = modelFinder.typeInference
}
