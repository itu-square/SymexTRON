package semantics

import com.typesafe.scalalogging.LazyLogging
import helper._
import kodkod.ast._
import kodkod.engine.Solution.Outcome
import kodkod.engine.Solver
import kodkod.engine.fol2sat.{TranslationLogger, TranslationLog}
import kodkod.engine.satlab.{ReductionStrategy, SATFactory}
import kodkod.engine.ucore.CRRStrategy
import kodkod.instance.{TupleSet, Bounds, Instance, Universe}
import monocle.Monocle
import semantics.Subst._
import semantics.domains.SHeap._
import semantics.domains.SMem._
import semantics.domains.SpatialDesc._
import semantics.domains._
import syntax.ast._

import scala.collection.JavaConverters._
import scala.collection.JavaConversions._
import scala.collection.immutable.Nil
import scala.language.higherKinds
import scalaz.Scalaz.{none, unfold => generate}
import scalaz.concurrent.Task
import scalaz.stream._
import scalaz.syntax.either._
import scalaz.syntax.monad._
import scalaz.syntax.std.option._
import scalaz.{Lens, Monoid, EitherT, \/}

class ModelFinder(symcounter: Counter, loccounter: Counter, defs: Map[Class, ClassDefinition],
                  beta: Int, delta: Int, optimistic: Boolean)
  extends LazyLogging {

  private type StringE[T] = String \/ T
  case class EvalState(ssymrels: Set[Relation], symnames: Set[Integer], constraints: Formula, ssymmap: Map[Symbols,Relation])
  private type EvalRes[T] = (EvalState, T)


  private
  def mergeEvalState(inState: EvalState, outState: EvalState): EvalState =
    EvalState(inState.ssymrels ++ outState.ssymrels, inState.symnames ++ outState.symnames, allFormulae(List(inState.constraints, outState.constraints)), inState.ssymmap ++ outState.ssymmap)

  var counter = 0

  object SymbolicSetRel {
    val self = Relation.unary("SymbolicSet")
    val locs = Relation.binary("SymbolicSet/locs")
    lazy val locsTyping = {
      val ss = Variable.unary("ss")
      ((ss.join(locs) in LocsRel.self) forAll (ss oneOf self)) and
        (locs.join(Expression.UNIV) in self)
    }
    val name = Relation.binary("SymbolicSet/name")
    lazy val nameTyping = {
      val s = Variable.unary("s")
      (s.join(name).one and (s.join(name) in Expression.INTS) forAll (s oneOf self)) and
        (name.join(Expression.UNIV) in self)
    }
    lazy val nameUniqueness = {
      val s1 = Variable.unary("s1")
      val s2 = Variable.unary("s2")
      ((s1.join(name) eq s2.join(name)) and (s1.join(name) eq Expression.NONE).not) implies (s1 eq s2) forAll ((s1 oneOf self) and (s2 oneOf self))
    }
  }

  object LocsRel {
    val self = Relation.unary("Locs")
    val name = Relation.binary("Locs/name")
    lazy val nameTyping = {
      val l = Variable.unary("l")
      (l.join(name).one and (l.join(name) in Expression.INTS)) forAll (l oneOf self) and
        (name.join(Expression.UNIV) in self)
    }
    lazy val nameUniqueness = {
      val l1 = Variable.unary("l1")
      val l2 = Variable.unary("l2")
      (l1 eq l2) iff (l1.join(name) eq l2.join(name)) forAll ((l1 oneOf self) and (l2 oneOf self))
    }
    val fields = Relation.ternary("Locs/fields")
    lazy val fieldsTyping = {
      val l = Variable.unary("l")
      val f = Variable.unary("f")
      val ol = Variable.unary("ol")
      (l.join(fields) in FieldsRel.self.product(self) and
        (f.join(l.join(fields)) in self forAll (f oneOf FieldsRel.self)) and
          ((l.join(fields).join(ol) in FieldsRel.self) forAll (ol oneOf self))
        ) forAll (l oneOf self) and
          (fields.join(Expression.UNIV).join(Expression.UNIV) in self)
    }
  }

  object VarsRel {
    val self = Relation.unary("Vars")
    val name = Relation.binary("Vars/name")
    lazy val nameTyping = {
      val v = Variable.unary("v")
      (v.join(name).one and (v.join(name) in Expression.INTS)) forAll (v oneOf self) and
        (name.join(Expression.UNIV) in self)
    }
    lazy val nameUniqueness = {
      val v1 = Variable.unary("v1")
      val v2 = Variable.unary("v2")
      ((v1 eq v2) iff (v1.join(name) eq v2.join(name))) forAll ((v1 oneOf self) and (v2 oneOf self))
    }
    val vals = Relation.binary("Vars/vals")
    lazy val valsTyping = {
      val v = Variable.unary("v")
      (v.join(vals) in LocsRel.self) forAll (v oneOf self) and
        (vals.join(Expression.UNIV) in self)
    }
  }

  object FieldsRel {
    val self = Relation.unary("Fields")
    val name = Relation.binary("Fields/name")
    lazy val nameTyping = {
      val f = Variable.unary("f")
      (f.join(name).one and (f.join(name) in Expression.INTS)) forAll (f oneOf self) and
        (name.join(Expression.UNIV) in self)
    }
    lazy val nameUniqueness = {
      val f1 = Variable.unary("f1")
      val f2 = Variable.unary("f2")
      ((f1 eq f2) iff (f1.join(name) eq f2.join(name))) forAll ((f1 oneOf self) and (f2 oneOf self))
    }
    val childs = Relation.unary("Fields$child")
    lazy val childsTyping = {
      val f = Variable.unary("f")
      f in self forAll (f oneOf childs)
    }
    val refs = Relation.unary("Fields$ref")
    lazy val refsTyping = {
      val f = Variable.unary("f")
      f in self forAll (f oneOf refs)
    }
    lazy val childsRefsDisjoint = {
      (childs intersection refs) eq Expression.NONE
    }
    lazy val childsDefFields = {
      allFormulae(defs.childfields.toList.map { field =>
        val f = Variable.unary("f")
        f in childs forAll (f oneOf fieldsrels(field))
      })
    }
    lazy val refsDefFields = {
      allFormulae(defs.reffields.toList.map { field =>
        val f = Variable.unary("f")
        f in refs forAll (f oneOf fieldsrels(field))
      })
    }
    val fieldsrels = (defs.childfields ++ defs.reffields).map(f => (f, Relation.unary(s"Field$$$f"))).toMap
  }

  object SymbolsRel {
    val self = Relation.unary("Symbols")
    val name = Relation.binary("Symbols/name")
    lazy val nameTyping = {
      val s = Variable.unary("s")
      (s.join(name).one and (s.join(name) in Expression.INTS) forAll (s oneOf self)) and
        (name.join(Expression.UNIV) in self)
    }
    lazy val nameUniqueness = {
      val s1 = Variable.unary("s1")
      val s2 = Variable.unary("s2")
      (s1 eq s2) iff (s1.join(name) eq s2.join(name)) forAll ((s1 oneOf self) and (s2 oneOf self))
    }
    val loc = Relation.binary("Symbols/loc")
    lazy val locTyping = {
      val s = Variable.unary("s")
      s.join(loc).one and (s.join(loc) in LocsRel.self) forAll (s oneOf self) and
        (loc.join(Expression.UNIV) in self)
    }
  }

  object TypesRel {
    val self = Relation.unary("Types")
    val isSubType = Relation.binary("Types/isSubType")
    lazy val isSubTypeTyping = {
      val t = Variable.unary("t")
      (t.join(isSubType) in self) forAll (t oneOf self) and
        (isSubType.join(Expression.UNIV) in self)
    }
    val typeOfSet = Relation.binary("Types/typeOfSet")
    lazy val typeOfSetTyping = {
      val ss = Variable.unary("ss")
      (ss.join(typeOfSet).one and (ss.join(typeOfSet) in self) forAll (ss oneOf SymbolicSetRel.self)) and
        (typeOfSet.join(Expression.UNIV) in SymbolicSetRel.self)
    }
    val typeOfSym = Relation.binary("Types/typeOfSym")
    lazy val typeOfSymTyping = {
      val s = Variable.unary("s")
      (s.join(typeOfSym).lone and (s.join(typeOfSym) in self) forAll (s oneOf SymbolsRel.self)) and
        (typeOfSym.join(Expression.UNIV) in SymbolsRel.self)
    }
    val typeOfLoc = Relation.binary("Types/typeOfLoc")
    lazy val typeOfLocTyping = {
      val l = Variable.unary("l")
      (l.join(typeOfLoc).one and (l.join(typeOfLoc) in self)) forAll (l oneOf LocsRel.self) and
        (typeOfLoc.join(Expression.UNIV) in LocsRel.self)
    }
    lazy val typeOfLocTypeOfSymEquality = {
      val s = Variable.unary("s")
      val l = Variable.unary("l")
      (s.join(SymbolsRel.loc) eq l) implies (s.join(typeOfSym) eq l.join(typeOfLoc)) forAll
        ((s oneOf SymbolsRel.self) and (l oneOf LocsRel.self))
    }
    lazy val typeOfLocTypeOfSetSubtyping = {
      val l = Variable.unary("l")
      val ss = Variable.unary("ss")
      val t = Variable.unary("t")
      val ts = Variable.unary("ts")
      ((l.join(typeOfLoc) eq t) and (ss.join(typeOfSet) eq ts) and (l in ss.join(SymbolicSetRel.locs)) implies
        (ts in t.join(isSubType))) forAll
          ((l oneOf LocsRel.self) and (ss oneOf SymbolicSetRel.self) and (t oneOf self) and (ts oneOf self))
    }
    lazy val typeOfFieldCorrectness = {
      val l = Variable.unary("l")
      val f = Variable.unary("f")
      val ol = Variable.unary("ol")
      val t = Variable.unary("t")
      val ot = Variable.unary("ot")
      allFormulae(defs.toList.map { case (c, cd) =>
        val supersOfC = defs.supertypes(c) + c
        val fieldsOfC = (defs.refsOf(supersOfC) ++ defs.childrenOf(supersOfC)).keySet
        val complementOfFieldsOfC = (defs.childfields ++ defs.reffields) diff fieldsOfC
        val fieldAbsence = allFormulae(complementOfFieldsOfC.toList.map { field =>
          (l.join(typeOfLoc) eq t) implies
            ((l product f product ol) in LocsRel.fields).not forAll
            ((ol oneOf LocsRel.self) and (l oneOf LocsRel.self) and
              (f oneOf FieldsRel.fieldsrels(field)) and (t oneOf TypesRel.typerels(c)))
        })
        val fieldTyping = allFormulae((cd.children ++ cd.refs).toList.map { case (field, (oc, crd)) =>
          val cardConstraint = (t in l.join(typeOfLoc).join(isSubType)) implies (crd match {
            case Single => f.join(l.join(LocsRel.fields)).one
            case Many => Formula.TRUE
            case Opt => f.join(l.join(LocsRel.fields)).lone
          }) forAll ((f oneOf FieldsRel.fieldsrels(field)) and (l oneOf LocsRel.self) and
            (t oneOf TypesRel.typerels(c)))
          val typingConstraint = (t in l.join(typeOfLoc).join(isSubType)) and ((l product f product ol) in LocsRel.fields `forSome` (ol oneOf LocsRel.self)) implies
            (ot in f.join(l.join(LocsRel.fields)).join(typeOfLoc).join(isSubType)) forAll
            ((f oneOf FieldsRel.fieldsrels(field)) and (l oneOf LocsRel.self) and
              (t oneOf TypesRel.typerels(c)) and (ot oneOf TypesRel.typerels(oc)))
          allFormulae(List(cardConstraint,typingConstraint))
        })
        allFormulae(List(fieldTyping, fieldAbsence))
      })
    }
    val typerels = defs.keys.map(c => (c,Relation.unary(s"Type$$${c.name}"))).toMap
  }

  object ReachabilityRel {
    val owner = Relation.binary("owner")
    lazy val ownerTyping = {
      val l = Variable.unary("l")
      (l.join(owner).lone and (l.join(owner) in LocsRel.self)) forAll(l oneOf LocsRel.self) and
        (owner.join(Expression.UNIV) in LocsRel.self)
    }
    lazy val ownerDefinition = {
      val l = Variable.unary("l")
      val ol = Variable.unary("ol")
      val f = Variable.unary("f")
      ((ol product l) in owner) iff
        ((l product f product ol) in LocsRel.fields `forSome` (f oneOf FieldsRel.childs)) forAll
                   ((l oneOf LocsRel.self) and (ol oneOf LocsRel.self))
    }
    lazy val ownerAcyclic = {
      val l = Variable.unary("l")
      ((l product l) in owner.closure).not forAll (l oneOf LocsRel.self)
    }
    val referencedBy = Relation.binary("referencedBy")
    lazy val referencedByTyping = {
      val l = Variable.unary("l")
      l.join(referencedBy) in LocsRel.self forAll(l oneOf LocsRel.self) and
        (referencedBy.join(Expression.UNIV) in LocsRel.self)
    }
    lazy val referencedByDefinition = {
      val l = Variable.unary("l")
      val ol = Variable.unary("ol")
      val f = Variable.unary("f")
      ((ol product l) in referencedBy) iff
        ((ol product l) in owner.closure) forAll
        //(((l product f product ol) in LocsRel.fields) `forSome` (f oneOf FieldsRel.refs)) forAll
              ((l oneOf LocsRel.self) and (ol oneOf LocsRel.self))
    }
    val reachableBy = Relation.binary("reachableBy")
    lazy val reachableByTyping = {
      val l = Variable.unary("l")
      l.join(reachableBy) in LocsRel.self forAll(l oneOf LocsRel.self) and
        (reachableBy.join(Expression.UNIV) in LocsRel.self)
    }
    lazy val reachableByDefinition = {
      val l = Variable.unary("l")
      val ol = Variable.unary("ol")
      ((ol product l) in reachableBy) iff
        (((ol product l) in owner.closure) or ((ol product l) in referencedBy.closure)) forAll ((l oneOf LocsRel.self) and (ol oneOf LocsRel.self))
    }
  }

  def freshSymbolicSetRel(id: Symbols): (Relation, Formula) = {
    counter = counter + 1
    val ss = Relation.unary(s"ConcreteSymbolicSet$counter")
    val s = Variable.unary("s")
    val nameExpr = IntConstant.constant(id).toExpression
    val nameConstraint = (s.join(SymbolicSetRel.name) eq nameExpr) forAll (s oneOf ss)
    val subsetConstraint = (s in SymbolicSetRel.self) forAll (s oneOf ss)
    (ss, nameConstraint and subsetConstraint)
  }

  def staticConstraints : Formula = {
   SymbolsRel.nameTyping and SymbolsRel.nameUniqueness and SymbolsRel.locTyping and
   SymbolicSetRel.locsTyping and  SymbolicSetRel.nameTyping and SymbolicSetRel.nameUniqueness and
   LocsRel.nameTyping and LocsRel.nameUniqueness and LocsRel.fieldsTyping and
   FieldsRel.nameTyping and FieldsRel.nameUniqueness and FieldsRel.childsTyping and FieldsRel.refsTyping and
   FieldsRel.childsRefsDisjoint and FieldsRel.childsDefFields and FieldsRel.refsDefFields and
   VarsRel.nameTyping and VarsRel.nameUniqueness and VarsRel.valsTyping and
   TypesRel.typeOfLocTyping and TypesRel.typeOfSymTyping and TypesRel.typeOfSetTyping and
   TypesRel.isSubTypeTyping and TypesRel.typeOfLocTypeOfSetSubtyping and TypesRel.typeOfLocTypeOfSymEquality and
   TypesRel.typeOfFieldCorrectness and ReachabilityRel.ownerTyping and ReachabilityRel.ownerDefinition and ReachabilityRel.ownerAcyclic and
   ReachabilityRel.referencedByTyping and ReachabilityRel.referencedByDefinition and ReachabilityRel.reachableByTyping and ReachabilityRel.reachableByDefinition
  }

  def classPresenceConstraint(clazz: Class): Formula = {
    val v = Variable.unary("v")
    val l = Variable.unary("l")
    val ol = Variable.unary("ol")
    val t = Variable.unary("t")
    (ol in v.join(VarsRel.vals)) and
      ((ol product l) in ReachabilityRel.reachableBy.reflexiveClosure) and
        (l.join(TypesRel.typeOfLoc) eq t) `forSome`
          ((v oneOf VarsRel.self) and (ol oneOf LocsRel.self) and (l oneOf LocsRel.self)) forAll
            (t oneOf TypesRel.typerels(clazz))
  }

  def fieldPresenceConstraint(field: (Class, Fields), fieldmap: Map[String, Int]): Formula = {
    val v = Variable.unary("v")
    val ol = Variable.unary("ol")
    val ool = Variable.unary("ool")
    val l = Variable.unary("l")
    val f = Variable.unary("f")
    val t = Variable.unary("t")
    (ol in v.join(VarsRel.vals)) and
      ((ol product l) in ReachabilityRel.reachableBy.reflexiveClosure) and
        (t in l.join(TypesRel.typeOfLoc).join(TypesRel.isSubType)) and
          (f.join(FieldsRel.name) eq IntConstant.constant(fieldmap(field._2)).toExpression) and
            ((l product f product ool) in LocsRel.fields) `forSome`
              ((v oneOf VarsRel.self) and (ol oneOf LocsRel.self) and (ool oneOf LocsRel.self) and (l oneOf LocsRel.self) and
                (f oneOf FieldsRel.self)) forAll (t oneOf TypesRel.typerels(field._1))
  }

  def calculateBounds(setsymexprels : Set[Relation], setsymmap: Map[Symbols, Relation], symnames: Set[Integer], locs: Set[Loc], fieldmap: Map[String, Integer], varmap: Map[String, Integer]) : Bounds = {
    val additionallocs = {
      // See if .max works instead of maximum
      val maxid = try { locs.map(_.id).max + 1 } catch { case e:UnsupportedOperationException => 0 }
      (maxid until (maxid + delta)).map(Loc)
    }
    val locobjs = locs.map(l => (Int.box(l.id), s"loc'${l.id}")).toMap
    val additionalocobjs =  additionallocs.map(l => (Int.box(l.id), s"loc'${l.id}")).toMap
    val allLocobjs = locobjs ++ additionalocobjs
    val symids = symnames.map(i => (i, s"sym'$i")).toMap
    val symbolicsets = (for ((r, i) <- setsymexprels.zipWithIndex) yield (r, s"set'$i")).toMap
    val types = for ((c, _) <- TypesRel.typerels) yield (c, s"type'${c.name}")
    val fieldobjs = fieldmap.map { case (field, i) => (field, (i, s"field'$field")) }
    val varobjs = varmap.map { case (vr, i) => (i, s"var'$vr") }
    val setsymnames: Set[Integer] = setsymmap.keySet.map(s => Int.box(s))
    val allsymbolicsets = symbolicsets.values.toSeq
    val atoms = symids.keySet ++ symids.values ++ allsymbolicsets ++ setsymnames ++ types.values ++
      allLocobjs.keySet ++ allLocobjs.values ++ fieldobjs.keySet ++ fieldobjs.values.flatMap { case (i,o) => List(i,o) } ++ varobjs.keySet ++ varobjs.values
    val universe = new Universe(atoms.asJava)
    val bounds = new Bounds(universe)
    val f = universe.factory

    for (intval <- allLocobjs.keySet ++ symids.keySet ++ fieldobjs.values.map(_._1) ++ varobjs.keySet)
      bounds.boundExactly(intval.intValue, f range (f tuple intval, f tuple intval))

    bounds.boundExactly(SymbolsRel.self, f setOf (symids.values.toSeq :_*))

    val symLocUpper = f noneOf 2
    for (symid <- symids.values.toSeq; locid <- allLocobjs.values.toSeq) symLocUpper.add((f tuple symid) product (f tuple locid))
    bounds.bound(SymbolsRel.loc, symLocUpper)

    for ((r, i) <- symbolicsets) bounds.boundExactly(r, f setOf i)
    bounds.boundExactly(SymbolicSetRel.self, f setOf (allsymbolicsets :_*))

    for (setsymname <- setsymnames)
      bounds.boundExactly(setsymname.intValue, f range (f tuple setsymname, f tuple setsymname))

    bounds.boundExactly(VarsRel.self, f setOf (varobjs.values.toSeq :_*))
    val varnameUpper = f noneOf 2
    for ((varname, varid) <- varobjs) varnameUpper.add((f tuple varid) product (f tuple varname))
    bounds.boundExactly(VarsRel.name, varnameUpper)
    val varvalsUpper = f noneOf 2
    for (varid <- varobjs.values.toSeq; locid <- allLocobjs.values.toSeq) varvalsUpper.add((f tuple varid) product (f tuple locid))
    bounds.bound(VarsRel.vals, varvalsUpper)

    for ((field, frelname) <- FieldsRel.fieldsrels) bounds.boundExactly(frelname, f setOf fieldobjs(field)._2)
    bounds.boundExactly(FieldsRel.self, f setOf (fieldobjs.values.map(_._2).toSeq :_*))
    bounds.bound(FieldsRel.childs, f setOf (fieldobjs.values.map(_._2).toSeq :_*))
    bounds.bound(FieldsRel.refs, f setOf (fieldobjs.values.map(_._2).toSeq :_*))
    val fieldnameUpper = f noneOf 2
    for ((fieldname, fieldid) <- fieldobjs.values) fieldnameUpper.add((f tuple fieldid) product (f tuple fieldname))
    bounds.bound(FieldsRel.name, fieldnameUpper)

    val ssetrellocsUpper = f noneOf 2
    for (locid <- allLocobjs.values.toSeq; sset <- allsymbolicsets) ssetrellocsUpper.add((f tuple sset) product (f tuple locid))
    bounds.bound(SymbolicSetRel.locs, ssetrellocsUpper)

    val ssetrelnameUpper = f noneOf 2
    for ((ssym, rel) <- setsymmap) ssetrelnameUpper.add((f tuple symbolicsets(rel)) product (f tuple Int.box(ssym)))
    bounds.bound(SymbolicSetRel.name, ssetrelnameUpper)

    bounds.boundExactly(LocsRel.self, f setOf (allLocobjs.values.toSeq :_*))
    val locsnameUpper = f noneOf 2
    for ((locname, locid) <- allLocobjs) locsnameUpper.add((f tuple locid) product (f tuple locname))
    bounds.boundExactly(LocsRel.name, locsnameUpper)

    val locsfieldsUpper = f noneOf 3
    for (locid <- allLocobjs.values; fieldid <- fieldobjs.values.map(_._2); olocid <- allLocobjs.values.toSeq)
      locsfieldsUpper.add((f tuple locid) product (f tuple fieldid) product (f tuple olocid))
    bounds.bound(LocsRel.fields, locsfieldsUpper)

    val symnameUpper = f noneOf 2
    for ((sname, sid) <- symids)
      symnameUpper.add((f tuple sid) product (f tuple sname))
    bounds.bound(SymbolsRel.name, symnameUpper)

    for ((c, trelname) <- TypesRel.typerels) bounds.boundExactly(trelname, f setOf types(c))
    bounds.boundExactly(TypesRel.self, f setOf (types.values.toSeq :_*))
    val stBounds = f noneOf 2
    for ((c, sc) <- defs.subtypesOrSelf.toList.flatMap { case (c, scs) => scs.toList.map(sc => (c,sc)) }) {
      stBounds.add((f tuple types(sc)) product (f tuple types(c)))
    }
    bounds.boundExactly(TypesRel.isSubType, stBounds)
    val typeOfSetUpper = f noneOf 2
    for (ss <- allsymbolicsets) {
      for (typ <- types.values.toSeq) {
        typeOfSetUpper.add((f tuple ss) product (f tuple typ))
      }
    }
    bounds.bound(TypesRel.typeOfSet, typeOfSetUpper)
    val typeOfSymUpper = f noneOf 2
    for (sid <- symids.values.toSeq) {
      for (typ <- types.values.toSeq) {
        typeOfSymUpper.add((f tuple sid) product (f tuple typ))
      }
    }
    bounds.bound(TypesRel.typeOfSym, typeOfSymUpper)
    val typeOfLocUpper = f noneOf 2
    for (lid <- allLocobjs.values.toSeq; typ <- types.values.toSeq) typeOfLocUpper.add((f tuple lid) product (f tuple typ))
    bounds.bound(TypesRel.typeOfLoc, typeOfLocUpper)

    val locReachUpper = f noneOf 2
    for (lid <- allLocobjs.values.toSeq; olid <- allLocobjs.values.toSeq) locReachUpper.add((f tuple lid) product (f tuple olid))
    bounds.bound(ReachabilityRel.owner, locReachUpper)
    bounds.bound(ReachabilityRel.referencedBy, locReachUpper)
    bounds.bound(ReachabilityRel.reachableBy, locReachUpper)
    bounds
  }

  def evalBoolExpr(b : BoolExpr[IsSymbolic.type], th : Map[Symbols, Relation], isNegated: Boolean = false)
  : String \/ EvalRes[Formula] = b match {
    case Eq(e1, e2) => evalBinaryBoolExpr(e1, _ eq _, e2, th, isNegated)
    case SetMem(e1, e2) => for {
        ee2 <- evalSetExpr(e2, th)
        (EvalState(rs2, is2, f2, th2), et2) = ee2
        formula = {
          val sym = Variable.unary("sym")
          val symInSyms = sym in et2
          (e1 match {
            case Symbol(symident) => sym.join(SymbolsRel.name) eq IntConstant.constant(symident).toExpression
          }) implies (if (isNegated) symInSyms.not else symInSyms) forAll (sym oneOf SymbolsRel.self)
        }
      } yield (EvalState(rs2, is2, allFormulae(List(formula, f2)), th2), formula)
    case SetSubEq(e1, e2) =>  evalBinaryBoolExpr(e1, _ in _, e2, th, isNegated)
    case True() => (EvalState(Set[Relation](), Set[Integer](), Formula.TRUE, th), if (isNegated) Formula.FALSE else Formula.TRUE).right
    case And(b1,b2) =>
      for {
        eb1 <- evalBoolExpr(b1, th, isNegated)
        (EvalState(rs1, is1, fs1, th1), r1) = eb1
        eb2 <- evalBoolExpr(b2, th1, isNegated)
        (EvalState(rs2, is2, fs2, th2), r2) = eb2
      } yield (EvalState(rs1 union rs2, is1 union is2, allFormulae(List(fs1, fs2)), th2), if (isNegated) anyFormulae(List(r1, r2)) else allFormulae(List(r1,r2)))
    case Not(b0) => for {
        eb <- evalBoolExpr(b0, th, !isNegated)
      } yield eb
  }

  def evalBinaryBoolExpr(e1: SetExpr[IsSymbolic.type], op: (Expression, Expression) => Formula, e2: SetExpr[IsSymbolic.type],
                         th: Map[Symbols, Relation], isNegated: Boolean): String \/ EvalRes[Formula] = {
    for {
      ee1 <- evalSetExpr(e1, th)
      (est1, et1) = ee1
      ee2 <- evalSetExpr(e2, est1.ssymmap)
      (est2, et2) = ee2
      formula = {
        val res = op(et1, et2)
        if (isNegated) res.not else res
      }
    } yield (mergeEvalState(est1, est2), formula)
  }

  // TODO Take into account symbol equivalence
  def evalSetExpr(e : SetExpr[IsSymbolic.type], th : Map[Symbols, Relation] = Map()): String \/ EvalRes[Expression] = e match {
    case SetLit(es) =>
      val et = if (es.isEmpty) Expression.NONE
        else {
          val sym = Variable.unary("sym")
          val loc = Variable.unary("loc")
          val ees = es.map {
            case Symbol(ident) =>
              sym.join(SymbolsRel.name) eq IntConstant.constant(ident).toExpression
          }.toList
          (allFormulae(List(anyFormulae(ees), loc in sym.join(SymbolsRel.loc))) `forSome` (sym oneOf SymbolsRel.self)) comprehension (loc oneOf LocsRel.self)
        }
      val s1 = Variable.unary("s1")
      val s2 = Variable.unary("s2")
      val diffConstraints = es.flatMap { case Symbol(ident) =>
          es.map {
            case Symbol(ident2) if ident != ident2 =>
              (s1.join(SymbolsRel.name) eq IntConstant.constant(ident).toExpression) and
                (s2.join(SymbolsRel.name) eq IntConstant.constant(ident2).toExpression) implies
                  (s1.join(SymbolsRel.loc) eq s2.join(SymbolsRel.loc)).not forAll
                    ((s1 oneOf SymbolsRel.self) and (s2 oneOf SymbolsRel.self))
            case _ => Formula.TRUE
          }
      }
      val symbols = es.filter(_.isInstanceOf[Symbol]).map(b => Int.box(b.asInstanceOf[Symbol].id))
      (EvalState(Set(), symbols.toSet, allFormulae(diffConstraints.toList), th), et).right[String]
    case Union(e1, e2) =>
      evalBinarySetExpr(e1, _ union _, e2, th)
    case Diff(e1, e2) =>
      evalBinarySetExpr(e1, _ difference _, e2, th)
    case ISect(e1, e2) =>
      evalBinarySetExpr(e1, _ intersection _, e2, th)
    case SetSymbol(ident) =>
      val (newrels, newformula, newth, rel) =
        if (th.contains(ident)) (Set[Relation](), Formula.TRUE, th, th(ident))
        else {
          val (s, nameConstraint) = freshSymbolicSetRel(ident)
          (Set(s), nameConstraint, th + (ident -> s), s)
        }
      val l = Variable.unary("l")
      val ss = Variable.unary("ss")
      (EvalState(newrels, Set(), newformula, newth), (l in ss.join(SymbolicSetRel.locs)) `forSome` (ss oneOf rel) comprehension (l oneOf LocsRel.self)).right[String]
  }

  def evalBinarySetExpr(e1: SetExpr[IsSymbolic.type], op: (Expression, Expression) => Expression, e2: SetExpr[IsSymbolic.type],
                        th : Map[Symbols, Relation]): String \/ EvalRes[Expression] = {
    for {
      ee1 <- evalSetExpr(e1,th)
      (EvalState(rs1, is1, f1, th1), et1) = ee1
      ee2 <- evalSetExpr(e2,th1)
      (EvalState(rs2, is2, f2, th2), et2) = ee2
    } yield (EvalState(rs1 union rs2, is1 union is2, allFormulae(List(f1, f2)), th2), op(et1, et2))
  }

  def concretise(smem: SMem): String \/ CMem = {
    concretisationConstraints(smem).flatMap{ case (cs, bs, _) =>
      println(s"SMEM: ${PrettyPrinter.pretty(smem.initStack)}; ${PrettyPrinter.pretty(smem.heap.svltion)};  ${PrettyPrinter.pretty(smem.heap.ssvltion)}; ${PrettyPrinter.pretty(smem.heap.initSpatial)}; ${PrettyPrinter.pretty(smem.heap.pure)}")
      findSolution(cs, bs) }.map(inst =>
      extractConcreteMemory(inst, smem.initStack.keySet))
  }

  def concretisationConstraints(smem: SMem): String \/ (Formula, Bounds, Map[String, Int]) = {
    def cardConstraint(s: Variable, crd: Cardinality): Formula = crd match {
      case Single => s.join(SymbolicSetRel.locs).one
      case Many => Formula.TRUE
      case Opt =>  s.join(SymbolicSetRel.locs).lone
    }
    val initEvalState = EvalState(Set(), Set(), Formula.TRUE, Map())
    val varIntMap = smem.initStack.keySet.zipWithIndex.toMap
    val varevalres = smem.initStack.foldLeft((initEvalState, List[Formula]()).right[String]) { (str, vinfo) =>
      val (vr, exp) = vinfo
      for {
        st <- str
        (evalState, constraints) = st
        eexp <- evalSetExpr(exp, evalState.ssymmap)
        (EvalState(rs,is,f,th), et) = eexp
        varconstraint = {
          val v = Variable.unary("v")
          (v.join(VarsRel.name) eq IntConstant.constant(varIntMap(vr)).toExpression) implies
                       (v.join(VarsRel.vals) eq et) forAll (v oneOf VarsRel.self)
        }
      } yield (EvalState(evalState.ssymrels ++ rs, evalState.symnames ++ is, evalState.constraints and f, th), varconstraint :: constraints)
    }.map { case (est, constraints) => (est, allFormulae(constraints)) }
    val ssvconstraints = allFormulae(smem.heap.ssvltion.toList.map { case (ssym, ssdesc) =>
      val s = Variable.unary("s")
      val t = Variable.unary("t")
      s.join(SymbolicSetRel.name) eq IntConstant.constant(ssym.id).toExpression implies
        (cardConstraint(s, ssdesc.crd) and (t in s.join(TypesRel.typeOfSet).join(TypesRel.isSubType))) forAll
        ((s oneOf SymbolicSetRel.self) and (t oneOf TypesRel.typerels(ssdesc.cl)))
    })
    val svconstraints = allFormulae(smem.heap.svltion.toList.map { case (sym, sdesc) =>
      sdesc match {
        case Loced(loc) =>
          val s = Variable.unary("s")
          val l = Variable.unary("l")
          (s.join(SymbolsRel.name) eq IntConstant.constant(sym.id).toExpression) and
            (l.join(LocsRel.name) eq IntConstant.constant(loc.id).toExpression) implies
              (s.join(SymbolsRel.loc) eq l) forAll ((s oneOf SymbolsRel.self) and (l oneOf LocsRel.self))
        case UnknownLoc(cl, ownership, descendantPools) =>
          val s = Variable.unary("s")
          val t = Variable.unary("t")
          (s.join(SymbolsRel.name) eq IntConstant.constant(sym.id).toExpression implies
            (t in s.join(TypesRel.typeOfSym).join(TypesRel.isSubType))) forAll ((s oneOf SymbolsRel.self) and (t oneOf TypesRel.typerels(cl)))
      }
    })
    val fieldIntMap = FieldsRel.fieldsrels.keySet.zipWithIndex.toMap
    def translateSpatial(initEvalState: EvalState) = smem.heap.initSpatial.foldLeft((initEvalState, List[Formula]()).right[String]) { (st, locinfo) =>
      val (loc, sdesc) = locinfo
      val l = Variable.unary("l")
      val t = Variable.unary("t")
      val t2 = Variable.unary("t2")
      val typeConstraint = (l.join(LocsRel.name) eq IntConstant.constant(loc.id).toExpression) implies
        (l.join(TypesRel.typeOfLoc) eq t) and (t2 in TypesRel.typerels(sdesc.cl)) and (sdesc.desctype match {
          case ExactDesc => t eq t2
          case AbstractDesc => t2 in t.join(TypesRel.isSubType)
          case PartialDesc(hasExact, possible) =>
            val exactConstraint = if (!hasExact) (t eq t2).not else Formula.TRUE
            val possibleConstraints = anyFormulae(possible.toList.map(c => TypesRel.typerels(c) in t.join(TypesRel.isSubType)))
            allFormulae(List(t2 in t.join(TypesRel.isSubType), anyFormulae(List(exactConstraint, possibleConstraints))))
      }) `forSome` ((t oneOf TypesRel.self) and (t2 oneOf TypesRel.self)) forAll (l oneOf LocsRel.self)
      for {
        evalres <- st
        (evalstate, constraints) = evalres
        fieldEvalRes <- (sdesc.children ++ sdesc.refs).foldLeft((evalstate, List[Formula]()).right[String]) { (st, fieldinfo) =>
          val (field, fieldval) = fieldinfo
          for {
            evalres <- st
            (evalstate, constraints) = evalres
            fieldvalres <- evalSetExpr(fieldval, evalstate.ssymmap)
            (fieldvalEvalState, fieldvalexp) = fieldvalres
            fieldconstraint = {
              val f = Variable.unary("f")
              (l.join(LocsRel.name) eq IntConstant.constant(loc.id).toExpression) and
                (f.join(FieldsRel.name) eq IntConstant.constant(fieldIntMap(field)).toExpression) implies
                  (f.product(fieldvalexp) in l.join(LocsRel.fields)) forAll
                    ((l oneOf LocsRel.self) and (f oneOf FieldsRel.self))
            }
          } yield (mergeEvalState(evalstate, fieldvalEvalState), fieldconstraint :: constraints)
        }
        (fieldEvalState, fieldConstraints) = fieldEvalRes
      } yield (mergeEvalState(evalstate, fieldEvalState), typeConstraint :: (fieldConstraints ++ constraints))
    }.map { case (est, constraints) => (est, allFormulae(constraints)) }

    for {
      ver <- varevalres
      (varEvalState, varConstraints) = ver
      epure <- evalBoolExpr(smem.heap.pure.foldLeft(True(): BoolExpr[IsSymbolic.type]) (And(_, _)), varEvalState.ssymmap, isNegated = false)
      (pureEvalState, pureConstraints) = epure
      // Consider using RWS monad
      iest = mergeEvalState(varEvalState, pureEvalState)
      spatialEvalRes <- translateSpatial(iest)
      (spatialEvalState, spatialConstraints) = spatialEvalRes
      est  = mergeEvalState(iest, spatialEvalState)
      allConstraints = allFormulae(
        List(staticConstraints, ssvconstraints, svconstraints, varConstraints, pureConstraints, spatialConstraints, est.constraints))
      bounds = calculateBounds(est.ssymrels, est.ssymmap, est.symnames, smem.heap.initSpatial.keySet, fieldIntMap.mapValues(Int.box), varIntMap.mapValues(Int.box))
    } yield (allConstraints, bounds, fieldIntMap)
  }

  def allFormulae(fs: List[Formula]): Formula = {
    implicit val allFormulaMonoid = Monoid.instance[Formula](_ and _, Formula.TRUE)
    fs.normalizeMonoidal
  }

  def anyFormulae(fs: List[Formula]): Formula = {
    implicit val anyFormulaMonoid = Monoid.instance[Formula](_ or _, Formula.FALSE)
    fs.normalizeMonoidal
  }

  def findSolution(constraints: Formula, bounds: Bounds): String \/ Instance = {
    val solver = new Solver
    solver.options.setSolver(SATFactory.DefaultSAT4J)
    solver.options.setLogTranslation(2)
    val solution = solver.solve(constraints, bounds)
    solution.outcome match {
      case Outcome.SATISFIABLE | Outcome.TRIVIALLY_SATISFIABLE => solution.instance.relationTuples.foreach(println); solution.instance.right
      case Outcome.UNSATISFIABLE | Outcome.TRIVIALLY_UNSATISFIABLE =>
        val proof = solution.proof
        val core = if (proof != null) { proof.minimize(new CRRStrategy()); proof.highLevelCore.toString } else "No core!"
        s""" |Unsatisfiable!
             |core:
             |${core}
             |
             |constraints:
             |$constraints
             |
             |bounds (relation):
             |${bounds.upperBounds.map(_.toString).mkString("\n")}
             |bounds (ints):
             |${bounds.intBounds}""".stripMargin.left
    }
  }

  def extractConcreteMemory(instance: Instance, vars: Set[Vars]): CMem = {
    def extractSet[K](ts: TupleSet): Set[K] = ts.foldLeft(Set[K]()) { (set, tuple) =>
      set + tuple.atom(0).asInstanceOf[K]
    }
    def extractMap[K,V](ts: TupleSet): Map[K,Set[V]] = ts.foldLeft(Map[K,Set[V]]()) { (map, tuple) =>
      map.adjust(tuple.atom(0).asInstanceOf[K])(_ + tuple.atom(1).asInstanceOf[V])
    }
    def extractTernary[A,B,C](ts: TupleSet): Set[(A,B,C)] = ts.foldLeft(Set[(A,B,C)]()) { (set, tuple) =>
      set + ((tuple.atom(0).asInstanceOf[A], tuple.atom(1).asInstanceOf[B], tuple.atom(2).asInstanceOf[C]))
    }
    val varVals = extractMap[String, String](instance.tuples(VarsRel.vals))
    val locName = extractMap[String, Int](instance.tuples(LocsRel.name)).mapValues(_.head.intValue)
    val typeOfLoc = extractMap[String, String](instance.tuples(TypesRel.typeOfLoc)).mapValues(_.head)
    val locFields = extractTernary[String, String, String](instance.tuples(LocsRel.fields))
    val stack = vars.map(v => (v, Set[Instances]())).toMap ++ varVals.foldLeft(Map[String, Set[Instances]]()) { (stack, kv) =>
      val (vr, set) = kv
      val varname = vr.replaceFirst("var'", "")
      stack + (varname -> varVals.get(vr).cata(_.map(locName), Set()))
    }
    val typeMap = typeOfLoc.foldLeft(Map[Instances, Class]()) { (typeMap, kv) =>
      val (loc, typ) = kv
      val typename = typ.replaceFirst("type'", "")
      typeMap + (locName(loc) -> Class(typename))
    }
    val (childRels, refRels) = locFields.partition { case (l,f,ss) => defs.childfields.contains(f.replaceFirst("field'","")) }
    def convertFieldmap(rels: Set[(String, String, String)]) : Map[Instances, Map[Fields, Set[Instances]]] = {
      rels.foldLeft(Map[Instances, Map[Fields, Set[Instances]]]()) { (map, rel) =>
        val (l, f, ol) = rel
        val locname = locName(l)
        val fieldname = f.replaceFirst("field'", "")
        val symLoc = locName(ol)
        map.updated(locname,
          map.get(locname).cata(fieldmap => fieldmap.updated(fieldname,
            fieldmap.get(fieldname).cata(locs => locs + symLoc, Set(symLoc))
          ), Map(fieldname -> Set(symLoc)))
        )
      }
    }
    val childMap = typeMap.mapValues(c => defs.childrenOf(defs.supertypes(c) + c).mapValues(_ => Set[Instances]())) ++ convertFieldmap(childRels)
    val refMap = typeMap.mapValues(c => defs.refsOf(defs.supertypes(c) + c).mapValues(_ => Set[Instances]())) ++ convertFieldmap(refRels)
    val extracted = CMem(stack, CHeap(typeMap, childMap, refMap))
    GarbageCollection.gc(extracted, resetlocs = true)
  }

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
            case Loced(l) => nmem.heap.currentSpatial(l).cl
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
      val sym = Symbol(symcounter.++())
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
      }.filter { case (loc, _) => defs.subtypesOrSelf(cl).contains(heap.currentSpatial(loc).cl) }.keySet
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
      case UnknownLoc(cl, ownership, descendantpool) =>
        // TODO check consistency via SAT
        val newLoc = Loc(loccounter.++())
        val (sdesc, nheap) = mkAbstractSpatialDesc(newLoc, cl, heap)
        val res = ownership match {
          case SUnowned =>
            // Can either alias existing locs with unknown owners or create new unowned locs
            val aliasLocs = relevantLocs(nheap, cl, isUnknown = false)
            val nnheap: SHeap = addNewLoc(newLoc, sdesc, Unowned, nheap)
            Process((newLoc, nnheap).right) ++
              (for (loc <- Process.emitAll(aliasLocs.toSeq)) yield {
                (loc, _sh_svltion.modify(_ + (sym -> Loced(loc)))(antialias(sym, nheap, loc))).right
              })
          case SRef =>
            // Can alias all existing locs or create new locs with unknown owners
            val aliasLocs = relevantLocs(nheap, cl, isUnknown = false)
            val nnheap: SHeap = addNewLoc(newLoc, sdesc, UnknownOwner, nheap)
            Process((newLoc, nnheap).right) ++
              (for (loc <- Process.emitAll(aliasLocs.toSeq)) yield
                (loc, _sh_svltion.modify(_ + (sym -> Loced(loc)))(antialias(sym, nheap, loc))).right)
          case SOwned(l, f) =>
            // Can alias existing locs with unknown owners or create new owned locs
            val aliasLocs = relevantLocs(nheap, cl, isUnknown = true)
            val nnheap: SHeap = addNewLoc(newLoc, sdesc, Owned(l,f), nheap)
            Process((newLoc, nnheap).right) ++
              (for (loc <- Process.emitAll(aliasLocs.toSeq)) yield
                (loc, (_sh_svltion.modify(_ + (sym -> Loced(loc))) andThen
                  _sh_locOwnership.modify(_ + (loc -> Owned(l,f))))(antialias(sym, nheap, loc))).right)
        }
        res
        /*
        TODO: Possible optimization
        val mentioningConstraints = heap.pure.filter(_.symbols.collect({ case \/-(s) => s }).contains(sym))
        if (mentioningConstraints.isEmpty) {
         ???
        } else ??? */
    }, Process(s"No such symbol: $sym".left))
  }

  def antialias(sym: Symbol, nheap: SHeap, loc: Loc): SHeap = {
    nheap.svltion.filter(_._2 == loc).keySet.foldLeft(nheap) { (stheap, sym2) => stheap.subst(sym2, sym) }
  }

  def unfoldFieldSet(loc: Loc, fieldSet: Map[Fields, (Class, Cardinality)], owned: Boolean): (SetSymbolValuation, Map[Fields, SetExpr[IsSymbolic.type]]) = {
    fieldSet.foldLeft((Map(): SetSymbolValuation, Map[Fields, SetExpr[IsSymbolic.type]]())) { (st, fieldkv) =>
      val (svltion, fields) = st
      fieldkv match {
        case (f, (cl, crd)) =>
          val sym = SetSymbol(symcounter.++())
          // TODO Partition descendant pools
          (svltion + (sym -> SSymbolDesc(cl, crd, if (owned) SOwned(loc, f) else SRef, Map())), fields + (f -> sym))
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
           nc <- EitherT[Process0,String,Class](Process.emitAll(dt.possible.toSeq).map(_.right))
           cd <- EitherT[Process0, String, ClassDefinition](defs.get(nc).cata(_.right, s"No such class: ${nc.name}".left).point[Process0])
           (psdesc, nheap) = unfoldAbstract(SpatialDesc(c, AbstractDesc, children, refs, descendantpool), cd, heap)
           res <- EitherT[Process0, String, (SpatialDesc, SHeap)](
                  if (containsTargetField(psdesc)) (psdesc, nheap).right.point[Process0]
                  else unfoldPartial(psdesc.cl, psdesc.desctype.asInstanceOf[PartialDesc], psdesc.children, psdesc.refs, psdesc.descendantpools, nheap))
        } yield res).run
      }
    }
    def unfoldAbstract(sdesc: SpatialDesc, cd: ClassDefinition, heap: SHeap): (SpatialDesc, SHeap) = {
      val (newsslvtionc, newchildren) = unfoldFieldSet(loc, cd.children, owned = true)
      val (newsslvtionr, newrefs) = unfoldFieldSet(loc, cd.refs, owned = false)
      val psdesctype = PartialDesc(hasExact = true, defs.directSubtypes(sdesc.cl))
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
        case ExactDesc => Process(s"Location ${PrettyPrinter.pretty(loc)} of type ${sdesc.cl.name} has no field $targetField".left)
        case AbstractDesc =>
          defs.get(sdesc.cl).cata({ cd =>
            val (psdesc, nheap) = unfoldAbstract(sdesc, cd, heap)
            if (containsTargetField(psdesc)) Process((psdesc, nheap).right)
            else unfoldPartial(psdesc.cl, psdesc.desctype.asInstanceOf[PartialDesc], psdesc.children, psdesc.refs, psdesc.descendantpools, nheap)
          }, Process(s"No such class: ${sdesc.cl.name}".left))
        case dt@PartialDesc(hasExact, possible) => unfoldPartial(sdesc.cl, dt, sdesc.children, sdesc.refs, sdesc.descendantpools, heap)
      }
    }, Process(s"No such location: ${PrettyPrinter.pretty(loc)}".left))
  }

  val typeInference = new TypeInference(defs)
}
