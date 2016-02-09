package semantics

import java.util

import kodkod.ast._
import kodkod.engine.satlab.SATFactory
import kodkod.engine.{Solution, Solver}
import kodkod.instance.{Bounds, TupleSet, Universe}

import _root_.syntax.ast
import syntax.ast._
import semantics.domains._
import semantics.domains.SpatialDesc._
import semantics.domains.SHeap._
import semantics.domains.SMem._
import semantics.Subst._
import helper._

import scala.collection.JavaConverters._
import scala.collection.mutable
import scalaz.{Scalaz, \/-, \/}
import Scalaz.{none, unfold => generate}
import scalaz.syntax.std.option._
import scalaz.syntax.either._
import scalaz.syntax.monad._
import scalaz.syntax.traverse._
import scalaz.concurrent.Task
import scalaz.stream._

import com.typesafe.scalalogging.LazyLogging

class ModelFinder(symcounter: Counter, loccounter: Counter, defs: Map[Class, ClassDefinition],
                  beta: Int, delta: Int, optimistic: Boolean)
  extends LazyLogging {

  private type StringE[T] = String \/ T
  private type EvalRes[T] = (Set[Relation], Set[Integer], Formula, T, Map[Symbols, Relation])

  var counter = 0

  val SymbolicSet = Relation.unary("SymbolicSet")
  val syms = Relation.binary("syms")


  val SymbolsRel = Relation.unary("Symbols")
  val name = Relation.binary("name")

  val Types = Relation.unary("Types")
  val isSubType = Relation.binary("isSubType")
  val typeOfS = Relation.binary("typeOfS")
  val typeOf = Relation.binary("typeOf")

  def freshSet : Relation = {
    counter = counter + 1
    Relation.unary(s"ConcreteSymbolicSet$counter")
  }

  def constraints : Formula = {
    val nameTyping = {
      val s = Variable.unary("s")
      (s.join(name).one and (s.join(name) in Expression.INTS) forAll (s oneOf SymbolsRel)) and
        (name.join(Expression.UNIV) in SymbolsRel)
    }
    val symsTyping = {
      val ss = Variable.unary("ss")
      ((ss.join(syms) in SymbolsRel) forAll (ss oneOf SymbolicSet)) and
        (syms.join(Expression.UNIV) in SymbolicSet)
    }
    val nameUniqueness = {
      val s1 = Variable.unary("s1")
      val s2 = Variable.unary("s2")
      (s1 eq s2) iff (s1.join(name) eq s2.join(name)) forAll ((s1 oneOf SymbolsRel) and (s2 oneOf SymbolsRel))
    }
    val typeOfSTyping = {
      val ss = Variable.unary("ss")
      (ss.join(typeOfS).one and (ss.join(typeOfS) in Types) forAll (ss oneOf SymbolicSet)) and
        (typeOfS.join(Expression.UNIV) in SymbolicSet)
    }
    val typeOfTyping = {
      val s = Variable.unary("s")
      (s.join(typeOf).one and (s.join(typeOf) in Types) forAll (s oneOf SymbolsRel)) and
        (typeOf.join(Expression.UNIV) in SymbolsRel)
    }
    nameTyping and nameUniqueness and symsTyping //and typeOfTyping and typeOfSTyping
  }


  def bounds(rs : Set[Relation], is : Set[Integer], minSymbols : Int) : Bounds = {
    val symbolintnames = (for (i <- 1 to (minSymbols - is.size)) yield {
      Int.box(symcounter.++)
    }).toSet ++ is

    val symbolids = symbolintnames.toList.sorted.map(i => s"sym'$i")
    val symbolicsets = for ((r, i) <- rs.zipWithIndex) yield (r, s"set'$i")
    val types = (for (c <- defs.keys) yield (c, s"type'${c.name}")).toMap
    val atoms =  symbolintnames ++ symbolids ++ symbolicsets.map(_._2) ++ types.values.toSeq
    val universe = new Universe(atoms.asJava)
    val bounds = new Bounds(universe)
    val f = universe.factory

    bounds.boundExactly(SymbolsRel, f setOf (symbolids :_*))
    for ((r, i) <- symbolicsets) bounds.boundExactly(r, f setOf i)
    bounds.boundExactly(SymbolicSet, f setOf (symbolicsets.map(_._2).toSeq :_*))

    for (symname <- symbolintnames)
      bounds.boundExactly(symname.intValue, f range (f tuple symname, f tuple symname))

    bounds.bound(syms, f allOf 2)
    val nameUpper = f noneOf 2
    for ((sid, sname) <- symbolids.zip(symbolintnames.toList.sorted))
      nameUpper.add((f tuple sid) product (f tuple sname))
    bounds.bound(name, nameUpper)

    bounds.boundExactly(Types, f setOf (types.values.toSeq :_*)) // TODO fix bounds
    val stBounds = f noneOf 2
    for ((c, sc) <- defs.subtypesOrSelf.toList.flatMap { case (c, scs) => scs.toList.map(sc => (c,sc)) }) {
      stBounds.add((f tuple types(sc)) product (f tuple types(c)))
    }
    bounds.boundExactly(isSubType, stBounds)
    val typeOfSUpper = f noneOf 2
    for (ss <- symbolicsets.map(_._2).toList) {
      for (typ <- types.values.toList) {
        typeOfSUpper.add((f tuple ss) product (f tuple typ))
      }
    }
    bounds.bound(typeOfS, typeOfSUpper)
    val typeOfUpper = f noneOf 2
    for (sid <- symbolids) {
      for (typ <- types.values.toList) {
        typeOfUpper.add((f tuple sid) product (f tuple typ))
      }
    }
    bounds.bound(typeOf, typeOfUpper)
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
          val symInSyms = sym in x.join(syms)
          (e1 match {
            case Symbol(symident) => sym.join(name) eq IntConstant.constant(symident).toExpression
          }) implies (if (isNegated) symInSyms.not else symInSyms) forAll ((sym oneOf SymbolsRel) and (x oneOf r2))
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
    case Not(b) => for {
        eb <- evalBoolExpr(b, th, !isNegated)
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
        val res = op(x1.join(syms), x2.join(syms))
        (if (isNegated) res.not else res) forAll ((x1 oneOf r1) and (x2 oneOf r2))
      }
    } yield (rs1 union rs2, is1 union is2, formula and f1 and f2, formula, th2)
  }

  def evalSetExpr(e : SetExpr[IsSymbolic.type], th : Map[Symbols, Relation] = Map()): String \/ EvalRes[Relation] = e match {
    case SetLit(es@_*) =>
      val s = freshSet
      val formula = {
        val ss = Variable.unary("ss")
        if (es.isEmpty) ss.join(syms) eq Expression.NONE forAll (ss oneOf s)
        else {
          val sym = Variable.unary("sym")
          val ees = es.map {
            case Symbol(ident) => sym.join(name) eq IntConstant.constant(ident).toExpression
          }.toList
          val ee1 :: ees1 = ees
          (ss.join(syms) eq (ees1.fold(ee1)(_ or _) comprehension (sym oneOf SymbolsRel))) forAll (ss oneOf s)
        }
      }
      val symbols = es.filter(_.isInstanceOf[Symbol]).map(b => Int.box(b.asInstanceOf[Symbol].id))
      (Set(s), symbols.toSet, formula, s, th).right[String]
    case Union(e1, e2) =>
      evalBinarySetExpr(e1, _ union _, e2, th)
    case Diff(e1, e2) =>
      evalBinarySetExpr(e1, _ difference _, e2, th)
    case ISect(e1, e2) =>
      evalBinarySetExpr(e1, _ intersection _, e2, th)
    case SetSymbol(ident) =>
      if (th.contains(ident)) (Set[Relation](), Set[Integer](), Formula.TRUE, th(ident), th).right[String]
      else {
        val s = freshSet
        val formula = Formula.TRUE
        (Set[Relation](s), Set[Integer](), formula, s, th + (ident -> s)).right[String]
      }
  }

  def evalBinarySetExpr(e1: SetExpr[IsSymbolic.type], op: (Expression, Expression) => Expression, e2: SetExpr[IsSymbolic.type],
                        th : Map[Symbols, Relation]): String \/ EvalRes[Relation] = {
    for {
      ee1 <- evalSetExpr(e1,th)
      (rs1, is1, f1, r1, th1) = ee1
      ee2 <- evalSetExpr(e2,th1)
      (rs2, is2, f2, r2, th2) = ee2
      s = freshSet
      formula = {
        val x = Variable.unary("x")
        val x1 = Variable.unary("x1")
        val x2 = Variable.unary("x2")
        x.join(syms) eq op(x1.join(syms),x2.join(syms)) forAll ((x oneOf s) and (x1 oneOf r1) and (x2 oneOf r2))
      }
    } yield (Set(s) union rs1 union rs2, is1 union is2, formula and f1 and f2, s, th2)
  }

  def relevantConstraints(e: SetExpr[IsSymbolic.type], p: Prop): (Prop, Prop) = {
    val (disj, norm) = p partition {
      case Eq(ISect(_,_), SetLit()) => true
      case _ => false
    }
    def rlv(syms: Set[Symbols], visited: Set[Symbols]): Prop = {
      val relevant = norm.filter((b : BoolExpr[IsSymbolic.type]) => (b.symbols.ids intersect syms).nonEmpty)
      val relevantsyms = relevant.symbols.ids diff visited
      relevant ++ (if (relevantsyms.nonEmpty)
                        rlv(relevantsyms, visited ++ syms)
                  else Set())
    }
    (disj, rlv(e.symbols.ids, Set()))
  }

  def ownershipConstraints(spatial: Spatial): Prop = ??? /* {
    spatial.flatMap{ case (sym, sd) => sd match {
      case SpatialDesc(c, typ, children, refs) => children.values.map(e => not(SetMem(Symbol(sym), e)))
    }}.toSet
  } */

  def partitionSet(ees: Set[Symbol], cl: Class): Process[Task, String \/ (Set[Symbol], SHeap)] = ???

  def simplify(e : SetExpr[IsSymbolic.type], heap:SHeap): (SetExpr[IsSymbolic.type], SHeap) = e match {
    case Union(e1, e2) =>
      val (es1, nheap) = simplify(e1, heap)
      val (es2, nnheap) = simplify(e2, nheap)
      (es1, es2) match {
        case (_:SetSymbol, _:SetSymbol) =>
      }
    case Diff(e1, e2) => ???
    case ISect(e1, e2) => ???
    case _ => (e, heap)
  }

  def findSet(e : SetExpr[IsSymbolic.type], heap: SHeap, setBound: Int, targetClass : Option[Class] = none):
      Process[Task, String \/ (Set[Symbol], SHeap)] =
          if (targetClass.cata(cl =>
                  typeInference.inferSetType(e, heap).cata(ec => defs.subtypesOrSelf(cl).contains(ec), true), false)) {
            findSet(e, heap, setBound, targetClass = none)
          } else {
            e match {
              case SetLit(es@_*) =>
                val ees = es.map{ case s:Symbol => s }.toSet
                targetClass.cata(cl => partitionSet(ees, cl), Process((ees, heap).right))
              case Union(e1, e2) => (e1, e2) match {
                case (x:SetSymbol, y: SetSymbol) => ???
                case (x:SetSymbol,  _)           => ???
                case (_, y: SetSymbol)           => ???
                case _                           => ???
              }
              case ISect(e1, e2) => (e1, e2) match {
                case (x:SetSymbol, y: SetSymbol) => ???
                case (x:SetSymbol,  _)           => ???
                case (_, y: SetSymbol)           => ???
                case _                           => ???
              }
              case Diff(e1, e2) =>
                (e1, e2) match {
                  case (_:SetSymbol, _: SetSymbol) => ???
                  case (_:SetSymbol,  _) => ???
                  case (_, _:SetSymbol) => ???
                  case _ =>
                    for {
                      e1r <- findSet(e1, heap, setBound, targetClass)
                      e12syms <- e1r traverseU { case (e1syms, nheap) =>
                        findSet(e2, nheap, setBound, targetClass) map (_.map { case (e2syms, nnheap) => (e1syms, e2syms, nnheap) })
                      } map (_.join)
                      res <- e12syms traverseU { case (e1syms, e2syms, nnheap) =>
                        for {
                          skirmishr <- symSkirmish(e1syms, e2syms, nnheap)
                          (diffsym, samesym, nnnheap) = skirmishr
                        } yield (samesym, nnnheap)
                      }
                    } yield res
                }
              case ssym:SetSymbol => findExplicitCardSet(ssym, setBound, heap)
            }
          }

  def symSame(syms1: Set[Symbol], syms2: Set[Symbol], heap: SHeap): (Set[Symbol], SHeap) = {
    val obvsame = syms1.intersect(syms2)
    val nsyms1 = syms1 diff obvsame
    val nsyms2 = syms2 diff obvsame
    val restsame = nsyms1 map { s1 =>
      nsyms2 collectFirst {
        // TODO: Represent a better way of getting these constraints
       case s2 if heap.pure.contains(Eq(SetLit(s1), SetLit(s2))) || heap.pure.contains(Eq(SetLit(s2), SetLit(s1))) =>
         (s1, s2)
      }
    } filter (_.nonEmpty) map (_.get)
    (obvsame ++ restsame.map(_._2), heap.subst_all(restsame.toMap))
  }

  def symDiff(syms1: Set[Symbol], syms2: Set[Symbol], heap: SHeap): Set[Symbol] = {
    def diff(syms1:Set[Symbol], syms2:Set[Symbol]): Set[Symbol] =
      syms1.filter(s1 => syms1.forall(s2 =>
        heap.pure.contains(Not(Eq(SetLit(s1), SetLit(s2)))) || heap.pure.contains(Not(Eq(SetLit(s2), SetLit(s1))))
      ))
    diff(syms1, syms2) ++ diff(syms2, syms1)
  }

  // This seems like a bad idea, maybe query the solver instead?
  def symSkirmish(syms1: Set[Symbol], syms2: Set[Symbol], heap: SHeap): Process[Task, (Set[Symbol], Set[Symbol], SHeap)] = {
    val (samesyms, uheap) = symSame(syms1, syms2, heap)
    val (nsyms1, nsyms2) = (syms1 -- samesyms, syms2 -- samesyms)
    val diffsyms = symDiff(nsyms1, nsyms2, uheap)
    val (nnsyms1, nnsyms2) = (syms1 -- diffsyms, syms2 -- diffsyms)
    if (nnsyms1.isEmpty || nnsyms2.isEmpty) Process((diffsyms, samesyms, uheap))
    else {
      Process.emitAll((nnsyms1 pairings nnsyms2 map { case (eqs, uneqs) =>
        val diff = uneqs.flatMap { case (s1, s2) => Set(s1, s2) }
        val same = eqs.map(_._1)
        val nheap = _sh_pure.modify(_ ++ uneqs.map { case (s1, s2) => Not(Eq(SetLit(s1), SetLit(s2))) })(heap.subst_all(eqs.map(_.swap).toMap))
        (same, diff, nheap)
      }).toSeq)
    }
  }

  def findExplicitCardSet(ssym: SetSymbol, setBound: Instances, heap: SHeap): Process[Nothing, \/[Nothing, (Set[Symbol], SHeap)]] = {
    def addSymbol(ssdesc: SSymbolDesc, st: Map[Symbol, SymbolDesc]): Map[Symbol, SymbolDesc] = {
      val sym = Symbol(symcounter.++)
      val symdesc = UnknownLoc(ssdesc.cl, ssdesc.ownership)
      val newst = st + (sym -> symdesc)
      newst
    }
    val ssdesc = heap.ssvltion(ssym)
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
      vl = SetLit(posVal.keys.toSeq: _*)
      nheap = _sh_svltion.modify(_ ++ posVal)(heap.subst(ssym, vl))
    } yield (posVal.keySet, nheap).right
  }

  def mkAbstractSpatialDesc(loc : Loc, cl : Class, heap: SHeap): (SpatialDesc, SHeap) = {
    val clSupers = defs.supertypes(cl)
    val (newssvltionc, children) = unfoldFieldSet(loc, defs.childrenOf(clSupers), owned = true)
    val (newssvltionr, refs) = unfoldFieldSet(loc, defs.refsOf(clSupers), owned = false)
    (SpatialDesc(cl, AbstractDesc, children, refs), _sh_ssvltion.modify(_ ++ newssvltionc ++ newssvltionr)(heap))
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
      case UnknownLoc(cl, ownership) => {
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
          (st._1 + (sym -> SSymbolDesc(cl, crd, if (owned) SOwned(loc, f) else SRef)), st._2)
      }
    }
  }

  def unfold(loc: Loc, targetField : Fields, heap: SHeap): Process0[String \/ (SpatialDesc, SHeap)] = {
    def containsTargetField(psdesc: SpatialDesc): Boolean = {
      psdesc.children.contains(targetField) || psdesc.refs.contains(targetField)
    }
    def unfoldPartial(c: Class, dt: PartialDesc, children: Map[Fields, SetExpr[IsSymbolic.type]],
                      refs: Map[Fields, SetExpr[IsSymbolic.type]], heap: SHeap): Process0[String \/ (SpatialDesc, SHeap)] = {
      val err = Process(s"Location ${PrettyPrinter.pretty(loc)} of type ${c.name} has no field $targetField".left)
      if (!optimistic) err
      else {
        (if(dt.hasExact) err else Process()) ++ (for {
           nc <- Process.emitAll(dt.possible.toSeq)
           cdr = defs.get(nc).cata(_.right, s"No such class: ${nc.name}".left)
           unfoldedr = cdr map { cd =>
             unfoldAbstract(SpatialDesc(c, AbstractDesc, children, refs), cd, heap)
           }
          res <- unfoldedr.traverse({ case (psdesc, nheap) =>
              if (containsTargetField(psdesc)) Process((psdesc, nheap).right)
              else unfoldPartial(psdesc.c, psdesc.desctype.asInstanceOf[PartialDesc], psdesc.children, psdesc.refs, nheap)
          })(pmn).map(_.join)
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
            else unfoldPartial(psdesc.c, psdesc.desctype.asInstanceOf[PartialDesc], psdesc.children, psdesc.refs, nheap)
          }, Process(s"No such class: ${sdesc.c.name}".left))
        case dt@PartialDesc(hasExact, possible) => unfoldPartial(sdesc.c, dt, sdesc.children, sdesc.refs, heap)
      }
    }, Process(s"No such location: ${PrettyPrinter.pretty(loc)}".left))
  }

  val typeInference = new TypeInference(defs)
}
