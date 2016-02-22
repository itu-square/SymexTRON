package semantics

import java.util

import kodkod.ast._
import kodkod.engine.{Solution, Solver}
import kodkod.instance.{Bounds, TupleSet, Universe}

import syntax.ast._
import semantics.domains._
import semantics.domains.SpatialDesc._
import semantics.domains.SHeap._
import semantics.domains.SMem._
import semantics.Subst._
import helper._

import scala.collection.JavaConverters._
import scalaz.{EitherT, Scalaz, \/}
import Scalaz.{none, unfold => generate}
import scalaz.syntax.std.option._
import scalaz.syntax.either._
import scalaz.concurrent.Task
import scalaz.stream._

import com.typesafe.scalalogging.LazyLogging

class ModelFinder(symcounter: Counter, loccounter: Counter, defs: Map[Class, ClassDefinition],
                  beta: Int, delta: Int, optimistic: Boolean)
  extends LazyLogging {

  private type StringE[T] = String \/ T
  private type EvalRes[T] = (Set[Relation], Set[Integer], Formula, T, Map[Symbols, Relation])

  var counter = 0

  object SymbolicSetRel {
    val self = Relation.unary("SymbolicSet")
    val syms = Relation.binary("SymbolicSet/syms")
    val symsTyping = {
      val ss = Variable.unary("ss")
      ((ss.join(SymbolicSetRel.syms) in SymbolsRel.self) forAll (ss oneOf SymbolicSetRel.self)) and
        (SymbolicSetRel.syms.join(Expression.UNIV) in SymbolicSetRel.self)
    }
    val name = Relation.binary("SymbolicSet/name")
    val nameTyping = {
      val s = Variable.unary("s")
      (s.join(name).lone and (s.join(name) in Expression.INTS) forAll (s oneOf self)) and
        (name.join(Expression.UNIV) in self)
    }
    val nameUniqueness = {
      val s1 = Variable.unary("s1")
      val s2 = Variable.unary("s2")
      (s1 eq s2) iff ((s1.join(name) eq s2.join(name)) and (s1.join(name) eq Expression.NONE).not) forAll ((s1 oneOf self) and (s2 oneOf self))
    }
  }

  object SymbolsRel {
    val self = Relation.unary("Symbols")
    val name = Relation.binary("Symbols/name")
    val nameTyping = {
      val s = Variable.unary("s")
      (s.join(SymbolsRel.name).one and (s.join(name) in Expression.INTS) forAll (s oneOf self)) and
        (name.join(Expression.UNIV) in self)
    }
    val nameUniqueness = {
      val s1 = Variable.unary("s1")
      val s2 = Variable.unary("s2")
      (s1 eq s2) iff (s1.join(name) eq s2.join(name)) forAll ((s1 oneOf self) and (s2 oneOf self))
    }
    val loc = Relation.binary("Symbols/loc")
  }

  object TypesRel {
    val self = Relation.unary("Types")
    val isSubType = Relation.binary("Types/isSubType")
    val typeOfS = Relation.binary("Types/typeOfS")
    val typeOfSTyping = {
      val ss = Variable.unary("ss")
      (ss.join(typeOfS).one and (ss.join(typeOfS) in self) forAll (ss oneOf SymbolicSetRel.self)) and
        (typeOfS.join(Expression.UNIV) in SymbolicSetRel.self)
    }
    val typeOf = Relation.binary("Types/typeOf")
    val typeOfTyping = {
      val s = Variable.unary("s")
      (s.join(typeOf).one and (s.join(typeOf) in typeOf) forAll (s oneOf SymbolsRel.self)) and
        (typeOf.join(Expression.UNIV) in SymbolsRel.self)
    }
  }

  def freshSymbolicSetRel(id: Option[Symbols]): (Relation, Formula) = {
    counter = counter + 1
    val ss = Relation.unary(s"ConcreteSymbolicSet$counter")
    val s = Variable.unary("s")
    val nameExpr = id.cata(i => IntConstant.constant(i).toExpression, Expression.NONE)
    val nameConstraint = s.join(SymbolicSetRel.name) eq nameExpr forAll (s oneOf ss)
    (ss, nameConstraint)
  }

  def constraints : Formula = {
    SymbolsRel.nameTyping and SymbolsRel.nameUniqueness and SymbolicSetRel.symsTyping and SymbolicSetRel.nameTyping and SymbolicSetRel.nameUniqueness //and typeOfTyping and typeOfSTyping
  }


  def bounds(rs : Set[Relation], symbolintnames: Set[Integer]) : Bounds = {
    val symbolids = symbolintnames.toList.sorted.map(i => s"sym'$i")
    val symbolicsets = for ((r, i) <- rs.zipWithIndex) yield (r, s"set'$i")
    val types = (for (c <- defs.keys) yield (c, s"type'${c.name}")).toMap
    val atoms =  symbolintnames ++ symbolids ++ symbolicsets.map(_._2) ++ types.values.toSeq
    val universe = new Universe(atoms.asJava)
    val bounds = new Bounds(universe)
    val f = universe.factory

    bounds.boundExactly(SymbolsRel.self, f setOf (symbolids :_*))
    for ((r, i) <- symbolicsets) bounds.boundExactly(r, f setOf i)
    bounds.boundExactly(SymbolicSetRel.self, f setOf (symbolicsets.map(_._2).toSeq :_*))

    for (symname <- symbolintnames)
      bounds.boundExactly(symname.intValue, f range (f tuple symname, f tuple symname))

    bounds.bound(SymbolicSetRel.syms, f allOf 2)
    val nameUpper = f noneOf 2
    for ((sid, sname) <- symbolids.zip(symbolintnames.toList.sorted))
      nameUpper.add((f tuple sid) product (f tuple sname))
    bounds.bound(SymbolsRel.name, nameUpper)

    bounds.boundExactly(TypesRel.self, f setOf (types.values.toSeq :_*))
    val stBounds = f noneOf 2
    for ((c, sc) <- defs.subtypesOrSelf.toList.flatMap { case (c, scs) => scs.toList.map(sc => (c,sc)) }) {
      stBounds.add((f tuple types(sc)) product (f tuple types(c)))
    }
    bounds.boundExactly(TypesRel.isSubType, stBounds)
    val typeOfSUpper = f noneOf 2
    for (ss <- symbolicsets.map(_._2).toList) {
      for (typ <- types.values.toList) {
        typeOfSUpper.add((f tuple ss) product (f tuple typ))
      }
    }
    bounds.bound(TypesRel.typeOfS, typeOfSUpper)
    val typeOfUpper = f noneOf 2
    for (sid <- symbolids) {
      for (typ <- types.values.toList) {
        typeOfUpper.add((f tuple sid) product (f tuple typ))
      }
    }
    bounds.bound(TypesRel.typeOf, typeOfUpper)
    bounds
  }

  def evalBoolExpr(b : BoolExpr[IsSymbolic.type], th : Map[Symbols, Relation], isNegated: Boolean = false)
  : String \/ EvalRes[Formula] = b match {
    case Eq(e1, e2) => evalBinaryBoolExpr(e1, _ eq _, e2, th, isNegated)
    case SetMem(e1, e2) => for {
        ee2 <- evalSetExpr(e2, th)
        (rs2, is2, f2, r2, th2) = ee2
        formula = {
          val sym = Variable.unary("sym")
          val x = Variable.unary("x")
          val symInSyms = sym in x.join(SymbolicSetRel.syms)
          (e1 match {
            case Symbol(symident) => sym.join(SymbolsRel.name) eq IntConstant.constant(symident).toExpression
          }) implies (if (isNegated) symInSyms.not else symInSyms) forAll ((sym oneOf SymbolsRel.self) and (x oneOf r2))
        }
      } yield (rs2, is2, formula and f2, formula, th2)
    case SetSubEq(e1, e2) =>  evalBinaryBoolExpr(e1, _ in _, e2, th, isNegated)
    case True() => (Set[Relation](), Set[Integer](), Formula.TRUE, Formula.TRUE, th).right
    case And(b1,b2) =>
      for {
        eb1 <- evalBoolExpr(b1, th, isNegated)
        (rs1, is1, fs1, r1, th1) = eb1
        eb2 <- evalBoolExpr(b2, th1, isNegated)
        (rs2, is2, fs2, r2, th2) = eb2
      } yield (rs1 union rs2, is1 union is2,  fs1 and fs2, if (isNegated) r1 or r2 else r1 and r2, th2)
    case Not(b0) => for {
        eb <- evalBoolExpr(b0, th, !isNegated)
        (rs1, is1, f1, r, th1) = eb
      } yield (rs1, is1, f1, r, th1)
  }

  def evalBinaryBoolExpr(e1: SetExpr[IsSymbolic.type], op: (Expression, Expression) => Formula, e2: SetExpr[IsSymbolic.type],
                         th: Map[Symbols, Relation], isNegated: Boolean): String \/ EvalRes[Formula] = {
    for {
      ee1 <- evalSetExpr(e1, th)
      (rs1, is1, f1, r1, th1) = ee1
      ee2 <- evalSetExpr(e2, th1)
      (rs2, is2, f2, r2, th2) = ee2
      formula = {
        val x1 = Variable.unary("x1")
        val x2 = Variable.unary("x2")
        val res = op(x1.join(SymbolicSetRel.syms), x2.join(SymbolicSetRel.syms))
        (if (isNegated) res.not else res) forAll ((x1 oneOf r1) and (x2 oneOf r2))
      }
    } yield (rs1 union rs2, is1 union is2, formula and f1 and f2, formula, th2)
  }

  def evalSetExpr(e : SetExpr[IsSymbolic.type], th : Map[Symbols, Relation] = Map()): String \/ EvalRes[Relation] = e match {
    case SetLit(es) =>
      val (s, nameConstraint) = freshSymbolicSetRel(none)
      val formula = {
        val ss = Variable.unary("ss")
        if (es.isEmpty) ss.join(SymbolicSetRel.syms) eq Expression.NONE forAll (ss oneOf s)
        else {
          val sym = Variable.unary("sym")
          val ees = es.map {
            case Symbol(ident) => sym.join(SymbolsRel.name) eq IntConstant.constant(ident).toExpression
          }.toList
          val ee1 :: ees1 = ees
          (ss.join(SymbolicSetRel.syms) eq (ees1.fold(ee1)(_ or _) comprehension (sym oneOf SymbolsRel.self))) forAll (ss oneOf s)
        }
      }
      val symbols = es.filter(_.isInstanceOf[Symbol]).map(b => Int.box(b.asInstanceOf[Symbol].id))
      (Set(s), symbols.toSet, formula and nameConstraint, s, th).right[String]
    case Part(syms) => ??? // TODO Implement
    case Union(e1, e2) =>
      evalBinarySetExpr(e1, _ union _, e2, th)
    case Diff(e1, e2) =>
      evalBinarySetExpr(e1, _ difference _, e2, th)
    case ISect(e1, e2) =>
      evalBinarySetExpr(e1, _ intersection _, e2, th)
    case SetSymbol(ident) =>
      if (th.contains(ident)) (Set[Relation](), Set[Integer](), Formula.TRUE, th(ident), th).right[String]
      else {
        val (s, nameConstraint) = freshSymbolicSetRel(ident.some)
        val formula = Formula.TRUE
        (Set[Relation](s), Set[Integer](), formula and nameConstraint, s, th + (ident -> s)).right[String]
      }
  }

  def evalBinarySetExpr(e1: SetExpr[IsSymbolic.type], op: (Expression, Expression) => Expression, e2: SetExpr[IsSymbolic.type],
                        th : Map[Symbols, Relation]): String \/ EvalRes[Relation] = {
    for {
      ee1 <- evalSetExpr(e1,th)
      (rs1, is1, f1, r1, th1) = ee1
      ee2 <- evalSetExpr(e2,th1)
      (rs2, is2, f2, r2, th2) = ee2
      (s, nameConstraint) = freshSymbolicSetRel(none)
      formula = {
        val x = Variable.unary("x")
        val x1 = Variable.unary("x1")
        val x2 = Variable.unary("x2")
        x.join(SymbolicSetRel.syms) eq op(x1.join(SymbolicSetRel.syms),x2.join(SymbolicSetRel.syms)) forAll ((x oneOf s) and (x1 oneOf r1) and (x2 oneOf r2))
      }
    } yield (Set(s) union rs1 union rs2, is1 union is2, formula and f1 and f2 and nameConstraint, s, th2)
  }

  def concretise(smem: SMem): String \/ CMem = { ??? }

  def partitionSet(ees: Set[Symbol], targetCl: Class, mem: SMem): Process[Task, (Set[Symbol], SMem)] = {
    def unfoldMore(mem: SMem, l: Loc, sdesc: SpatialDesc, supers: Set[Class]): SMem = {
      val (ssvltionc, newchildren) = unfoldFieldSet(l, defs.childrenOf(supers), owned = true)
      val (ssvltionr, newrefs) = unfoldFieldSet(l, defs.refsOf(supers), owned = false)
      val nmem =
         _sm_heap.modify(_sh_currentSpatial.modify(
           _.updated(l, (_sd_c.set(targetCl) andThen _sd_children.modify(_ ++ newchildren)
             andThen _sd_desctype.set(AbstractDesc) andThen _sd_refs.modify(_ ++ newrefs)) (sdesc))) andThen
           _sh_ssvltion.modify(_ ++ ssvltionc ++ ssvltionr))(mem)
      nmem
    }
    ees.foldLeft(Process((Set[Symbol](), mem))) { (p, sym) =>
      for {
        ssnmem <- p
        (ss, nmem) = ssnmem
        res <- {
          val symsvltion = nmem.heap.svltion(sym)
          val symc = symsvltion match {
            case Loced(l) => nmem.heap.currentSpatial(l).c
            case UnknownLoc(ncl, ownership, descendantpool) => ncl
          }
          if (defs.subtypesOrSelf(targetCl).contains(symc)) Process((ss + sym, nmem))
          else if (defs.subtypes(symc).contains(targetCl)) {
            symsvltion match {
              case Loced(l) =>
                val sdesc = nmem.heap.currentSpatial(l)
                sdesc.desctype match {
                  case ExactDesc => Process((ss, nmem))
                  case AbstractDesc =>
                    val supers = defs.supertypes(targetCl) diff defs.supertypes(symc)
                    val nnmem: SMem = unfoldMore(nmem, l, sdesc, supers)
                    Process((ss, nmem), (ss + sym, nnmem))
                  case PartialDesc(hasExact, possible) =>
                    val possibleSupers = possible.intersect(defs.supertypes(symc))
                    Process((ss, nmem)) ++ (for {
                      psuper <- Process.emitAll(possibleSupers.toSeq)
                      unfolded = {
                        val supers = defs.supertypes(targetCl) diff (defs.supertypes(psuper) + psuper)
                        val nnheap = unfoldMore(nmem, l, sdesc, supers)
                        (ss + sym, nnheap)
                      }
                    } yield unfolded)
                }
              case UnknownLoc(ncl, ownership, descendantpool) =>
                Process((ss, nmem), (ss + sym, (_sm_heap ^|-> _sh_svltion).modify(_.updated(sym, UnknownLoc(targetCl, ownership, descendantpool)))(nmem)))
            }
          }
          else Process((ss, nmem))
        }
      } yield res
    }
  }

  // TODO actually implement optimization
  def simplify(e : SetExpr[IsSymbolic.type], mem:SMem): (SetExpr[IsSymbolic.type], SMem) = e match {
    case Union(e1, e2) =>
      val (es1, nheap) = simplify(e1, mem)
      val (es2, nnheap) = simplify(e2, nheap)
      (Union(es1, es2), nnheap)
    case Diff(e1, e2) =>
      val (es1, nheap) = simplify(e1, mem)
      val (es2, nnheap) = simplify(e2, nheap)
      (Diff(es1, es2), nnheap)
    case ISect(e1, e2) =>
      val (es1, nheap) = simplify(e1, mem)
      val (es2, nnheap) = simplify(e2,nheap)
      (ISect(es1, es2), nnheap)
    case _ => (e, mem)
  }

  def findSet(e : SetExpr[IsSymbolic.type], mem: SMem, setBound: Int, targetClass : Option[Class] = none):
      Process[Task, String \/ (Set[Symbol], SMem)] =
          if (targetClass.cata(cl =>
                  typeInference.inferSetType(e, mem.heap).cata(ec => defs.subtypesOrSelf(cl).contains(ec), true), false)) {
            findSet(e, mem, setBound, targetClass = none)
          } else {
            // TODO Implement correctly to account for symbol equality
            def findBinary(e1: SetExpr[IsSymbolic.type], e2: SetExpr[IsSymbolic.type], op: (Set[Symbol], Set[Symbol]) => Set[Symbol], mem: SMem): TProcess[\/[String, (Set[Symbol], SMem)]] = {
              (for {
                e1r <- EitherT[TProcess, String, (Set[Symbol], SMem)](findSet(e1, mem, setBound, targetClass))
                (syms1, nheap) = e1r
                e2r <- EitherT[TProcess, String, (Set[Symbol], SMem)](findSet(e2, mem, setBound, targetClass))
                (syms2, nnheap) = e2r
              } yield (op(syms1, syms2), nnheap)).run
            }
            val (eSimp, memSimp) = simplify(e, mem)
            eSimp match {
              case SetLit(es) =>
                val ees = es.map{ case s:Symbol => s }.toSet
                targetClass.cata(cl => partitionSet(ees, cl, memSimp).map(_.right), Process((ees, memSimp).right))
              case Part(syms) => ???
              case Union(e1, e2) =>
                findBinary(e1, e2, _ union _, memSimp)
              case ISect(e1, e2) =>
                findBinary(e1, e2, _ intersect _, memSimp)
              case Diff(e1, e2) =>
                findBinary(e1, e2, _ diff _, memSimp)
              case ssym:SetSymbol => findExplicitCardSet(ssym, setBound, memSimp)
            }
          }

  def symSame(syms1: Set[Symbol], syms2: Set[Symbol], mem: SMem): (Set[Symbol], SMem) = {
    val obvsame = syms1.intersect(syms2)
    val nsyms1 = syms1 diff obvsame
    val nsyms2 = syms2 diff obvsame
    val restsame = nsyms1 map { s1 =>
      nsyms2 collectFirst {
        // TODO: Represent a better way of getting these constraints
       case s2 if mem.heap.pure.contains(Eq(SetLit(Seq(s1)), SetLit(Seq(s2)))) || mem.heap.pure.contains(Eq(SetLit(Seq(s2)), SetLit(Seq(s1)))) =>
         (s1, s2)
      }
    } filter (_.nonEmpty) map (_.get)
    (obvsame ++ restsame.map(_._2), mem.subst_all(restsame.toMap))
  }

  def symDiff(syms1: Set[Symbol], syms2: Set[Symbol], mem: SMem): Set[Symbol] = {
    def diff(syms1:Set[Symbol], syms2:Set[Symbol]): Set[Symbol] =
      syms1.filter(s1 => syms1.forall(s2 =>
        mem.heap.pure.contains(Not(Eq(SetLit(Seq(s1)), SetLit(Seq(s2))))) || mem.heap.pure.contains(Not(Eq(SetLit(Seq(s2)), SetLit(Seq(s1)))))
      ))
    diff(syms1, syms2) ++ diff(syms2, syms1)
  }

  // This seems like a bad idea, maybe query the solver instead?
  def symSkirmish(syms1: Set[Symbol], syms2: Set[Symbol], mem: SMem): Process[Task, (Set[Symbol], Set[Symbol], SMem)] = {
    val (samesyms, uheap) = symSame(syms1, syms2, mem)
    val (nsyms1, nsyms2) = (syms1 -- samesyms, syms2 -- samesyms)
    val diffsyms = symDiff(nsyms1, nsyms2, uheap)
    val (nnsyms1, nnsyms2) = (syms1 -- diffsyms, syms2 -- diffsyms)
    if (nnsyms1.isEmpty || nnsyms2.isEmpty) Process((diffsyms, samesyms, uheap))
    else {
      Process.emitAll((nnsyms1 pairings nnsyms2 map { case (eqs, uneqs) =>
        val diff = uneqs.flatMap { case (s1, s2) => Set(s1, s2) }
        val same = eqs.map(_._1)
        val nmem = (_sm_heap ^|-> _sh_pure).modify(_ ++ uneqs.map { case (s1, s2) => Not(Eq(SetLit(Seq(s1)), SetLit(Seq(s2)))) })(mem.subst_all(eqs.map(_.swap).toMap))
        (same, diff, nmem)
      }).toSeq)
    }
  }

  def findExplicitCardSet(ssym: SetSymbol, setBound: Instances, mem: SMem): Process0[String \/ (Set[Symbol], SMem)] = {
    def addSymbol(ssdesc: SSymbolDesc, st: Map[Symbol, SymbolDesc]): Map[Symbol, SymbolDesc] = {
      val sym = Symbol(symcounter.++)
      // TODO Fix descendantpool to be partitioned
      val symdesc = UnknownLoc(ssdesc.cl, ssdesc.ownership, ssdesc.descendantPools)
      val newst = st + (sym -> symdesc)
      newst
    }
    val ssdesc = mem.heap.ssvltion(ssym)
    val (lb, ub) = ssdesc.crd match {
      case Single => (1, 1)
      case Many => (0, setBound)
      case Opt => (0, 1)
    }
    val posVals = Process.emitAll(generate((0, Map[Symbol, SymbolDesc]())) { case (i, st) =>
      if (i < lb) {
        val newst = addSymbol(ssdesc, st)
        (none[SymbolValuation], (i + 1, newst)).some
      } else if (i == lb) (st.some, (i + 1, st)).some
      else if (i > ub) none
      else {
        val newst = addSymbol(ssdesc, st)
        (newst.some, (i + 1, newst)).some
      }
    } filter (_.nonEmpty) map (_.get))
    for {
      posVal <- posVals
      vl = SetLit(posVal.keys.toSeq)
      nmem = (_sm_heap ^|-> _sh_svltion).modify(_ ++ posVal)(mem.subst(ssym, vl))
    } yield (posVal.keySet, nmem).right
  }

  def mkAbstractSpatialDesc(loc : Loc, cl : Class, heap: SHeap): (SpatialDesc, SHeap) = {
    val clSupers = defs.supertypes(cl)
    val (newssvltionc, children) = unfoldFieldSet(loc, defs.childrenOf(clSupers), owned = true)
    val (newssvltionr, refs) = unfoldFieldSet(loc, defs.refsOf(clSupers), owned = false)
    (SpatialDesc(cl, AbstractDesc, children, refs, Map()), _sh_ssvltion.modify(_ ++ newssvltionc ++ newssvltionr)(heap))
  }

  def findLoc(sym: Symbol, heap: SHeap): Process0[String \/ (Loc, SHeap)] = {
    def relevantLocs(nheap: SHeap, cl: Class, isUnknown: Boolean): Set[Loc] = {
      // TODO: Filter safely
      nheap.locOwnership.filter { case (loc, ownership) => ownership match {
        case UnknownOwner => true
        case NewlyCreated => false
        case _ => !isUnknown  }
      }.filter { case (loc, _) => defs.subtypesOrSelf(cl).contains(heap.currentSpatial(loc).c) }.keySet
    }
    def addNewLoc(newLoc: Loc, sdesc: SpatialDesc, ownership: Ownership, nheap: SHeap): SHeap = {
      val nnheap = (_sh_svltion.modify(_ + (sym -> Loced(newLoc))) andThen
        _sh_locOwnership.modify(_ + (newLoc -> ownership)) andThen
        _sh_initSpatial.modify(_ + (newLoc -> sdesc)) andThen
        _sh_currentSpatial.modify(_ + (newLoc -> sdesc))) (nheap)
      nnheap
    }
    heap.svltion.get(sym).cata({
      case Loced(l) => Process((l, heap).right)
      case UnknownLoc(cl, ownership, descendantpool) => {
        // TODO check consistency via SAT
        val newLoc = Loc(loccounter.++)
        val (sdesc, nheap) = mkAbstractSpatialDesc(newLoc, cl, heap)
        ownership match {
          case SUnowned =>
            // Can either alias existing locs with unknown owners or create new unowned locs
            val aliasLocs = relevantLocs(nheap, cl, isUnknown = true)
            val nnheap: SHeap = addNewLoc(newLoc, sdesc, Unowned, nheap)
            Process((newLoc, nnheap).right) ++
              (for (loc <- Process.emitAll(aliasLocs.toSeq)) yield
                (loc, (_sh_svltion.modify(_ + (sym -> Loced(newLoc))) andThen
                _sh_locOwnership.modify(_ + (newLoc -> Unowned)))(antialias(sym, nheap, loc))).right)
          case SRef =>
            // Can alias all existing locs or create new locs with unknown owners
            val aliasLocs = relevantLocs(nheap, cl, isUnknown = false)
            val nnheap: SHeap = addNewLoc(newLoc, sdesc, UnknownOwner, nheap)
            Process((newLoc, nnheap).right) ++
              (for (loc <- Process.emitAll(aliasLocs.toSeq)) yield
                (loc, _sh_svltion.modify(_ + (sym -> Loced(newLoc)))(antialias(sym, nheap, loc))).right)
          case SOwned(l, f) =>
            // Can alias existing locs with unknown owners or create new owned locs
            val aliasLocs = relevantLocs(nheap, cl, isUnknown = true)
            val nnheap: SHeap = addNewLoc(newLoc, sdesc, Owned(l,f), nheap)
            Process((newLoc, nnheap).right) ++
              (for (loc <- Process.emitAll(aliasLocs.toSeq)) yield
                (loc, (_sh_svltion.modify(_ + (sym -> Loced(newLoc))) andThen
                  _sh_locOwnership.modify(_ + (newLoc -> Owned(l,f))))(antialias(sym, nheap, loc))).right)
        }
        /*
        TODO: Possible optimization
        val mentioningConstraints = heap.pure.filter(_.symbols.collect({ case \/-(s) => s }).contains(sym))
        if (mentioningConstraints.isEmpty) {
         ???
        } else ??? */
      }
    }, Process(s"No such symbol: $sym".left))
  }

  def antialias(sym: Symbol, nheap: SHeap, loc: Loc): SHeap = {
    nheap.svltion.filter(_._2 == loc).keySet.foldLeft(nheap) { (stheap, sym2) => stheap.subst(sym2, sym) }
  }

  def unfoldFieldSet(loc: Loc, fieldSet: Map[Fields, (Class, Cardinality)], owned: Boolean): (SetSymbolValuation, Map[Fields, SetExpr[IsSymbolic.type]]) = {
    fieldSet.foldLeft((Map(): SetSymbolValuation, Map[Fields, SetExpr[IsSymbolic.type]]())) { (st, fieldkv) =>
      fieldkv match {
        case (f, (cl, crd)) =>
          val sym = SetSymbol(symcounter.++)
          // TODO Partition descendant pools
          (st._1 + (sym -> SSymbolDesc(cl, crd, if (owned) SOwned(loc, f) else SRef, Map())), st._2)
      }
    }
  }

  def unfold(loc: Loc, targetField : Fields, heap: SHeap): Process0[String \/ (SpatialDesc, SHeap)] = {
    def containsTargetField(psdesc: SpatialDesc): Boolean = {
      psdesc.children.contains(targetField) || psdesc.refs.contains(targetField)
    }
    def unfoldPartial(c: Class, dt: PartialDesc, children: Map[Fields, SetExpr[IsSymbolic.type]],
                      refs: Map[Fields, SetExpr[IsSymbolic.type]], descendantpool: DescendantPools, heap: SHeap): Process0[String \/ (SpatialDesc, SHeap)] = {
      val err = Process(s"Location ${PrettyPrinter.pretty(loc)} of type ${c.name} has no field $targetField".left)
      if (!optimistic) err
      else {
        (if(dt.hasExact) err else Process()) ++ (for {
           nc <- Process.emitAll(dt.possible.toSeq)
           cdr = defs.get(nc).cata(_.right, s"No such class: ${nc.name}".left)
           unfoldedr = cdr map { cd =>
             unfoldAbstract(SpatialDesc(c, AbstractDesc, children, refs, descendantpool), cd, heap)
           }
          res <- unfoldedr.traverse({ case (psdesc, nheap) =>
              if (containsTargetField(psdesc)) Process((psdesc, nheap).right)
              else unfoldPartial(psdesc.c, psdesc.desctype.asInstanceOf[PartialDesc], psdesc.children, psdesc.refs, psdesc.descendantpools, nheap)
          })(pmn).map(_.flatMap(identity))
        } yield res)
      }
    }
    def unfoldAbstract(sdesc: SpatialDesc, cd: ClassDefinition, heap: SHeap): (SpatialDesc, SHeap) = {
      val (newsslvtionc, newchildren) = unfoldFieldSet(loc, cd.children, owned = true)
      val (newsslvtionr, newrefs) = unfoldFieldSet(loc, cd.refs, owned = true)
      val psdesctype = PartialDesc(hasExact = true, defs.directSubtypes(sdesc.c))
      val pschildren = sdesc.children ++ newchildren
      val psrefs = sdesc.refs ++ newrefs
      val psdesc = (_sd_desctype.set(psdesctype) andThen
        _sd_children.set(pschildren) andThen
        _sd_refs.set(psrefs)) (sdesc)
      val nheap = (_sh_currentSpatial.modify(_ + (loc -> psdesc)) andThen
                  _sh_initSpatial.modify(_ + (loc -> psdesc)) andThen
                  _sh_ssvltion.modify(_ ++ newsslvtionc ++ newsslvtionr))(heap)
      (psdesc, nheap)
    }
    heap.currentSpatial.get(loc).cata({ sdesc =>
      if (containsTargetField(sdesc)) Process((sdesc, heap).right)
      else sdesc.desctype match {
        case ExactDesc => Process(s"Location ${PrettyPrinter.pretty(loc)} of type ${sdesc.c.name} has no field $targetField".left)
        case AbstractDesc =>
          defs.get(sdesc.c).cata({ cd =>
            val (psdesc, nheap) = unfoldAbstract(sdesc, cd, heap)
            if (containsTargetField(psdesc)) Process((psdesc, nheap).right)
            else unfoldPartial(psdesc.c, psdesc.desctype.asInstanceOf[PartialDesc], psdesc.children, psdesc.refs, psdesc.descendantpools, nheap)
          }, Process(s"No such class: ${sdesc.c.name}".left))
        case dt@PartialDesc(hasExact, possible) => unfoldPartial(sdesc.c, dt, sdesc.children, sdesc.refs, sdesc.descendantpools, heap)
      }
    }, Process(s"No such location: ${PrettyPrinter.pretty(loc)}".left))
  }

  val typeInference = new TypeInference(defs)
}
