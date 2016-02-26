package semantics

import com.typesafe.scalalogging.LazyLogging
import helper._
import kodkod.ast._
import kodkod.engine.Solution.Outcome
import kodkod.engine.Solver
import kodkod.engine.satlab.SATFactory
import kodkod.instance.{Bounds, Instance, Universe}
import semantics.Subst._
import semantics.domains.SHeap._
import semantics.domains.SMem._
import semantics.domains.SpatialDesc._
import semantics.domains._
import syntax.ast._

import scala.collection.JavaConverters._
import scala.language.higherKinds
import scalaz.Scalaz.{none, unfold => generate}
import scalaz.concurrent.Task
import scalaz.stream._
import scalaz.syntax.either._
import scalaz.syntax.monad._
import scalaz.syntax.std.option._
import scalaz.{EitherT, \/}

class ModelFinder(symcounter: Counter, loccounter: Counter, defs: Map[Class, ClassDefinition],
                  beta: Int, delta: Int, optimistic: Boolean)
  extends LazyLogging {

  private type StringE[T] = String \/ T
  case class EvalState(ssymrels: Set[Relation], symnames: Set[Integer], constraints: Formula, ssymmap: Map[Symbols,Relation])
  private type EvalRes[T] = (EvalState, T)


  def mergeEvalState(inState: EvalState, outState: EvalState): EvalState =
    EvalState(inState.ssymrels ++ outState.ssymrels, inState.symnames ++ outState.symnames, inState.constraints and outState.constraints, inState.ssymmap ++ outState.ssymmap)

  var counter = 0

  object SymbolicSetRel {
    val self = Relation.unary("SymbolicSet")
    val syms = Relation.binary("SymbolicSet/syms")
    lazy val symsTyping = {
      val ss = Variable.unary("ss")
      ((ss.join(syms) in SymbolsRel.self) forAll (ss oneOf self)) and
        (syms.join(Expression.UNIV) in self)
    }
    val name = Relation.binary("SymbolicSet/name")
    lazy val nameTyping = {
      val s = Variable.unary("s")
      (s.join(name).lone and (s.join(name) in Expression.INTS) forAll (s oneOf self)) and
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
      val ss = Variable.unary("s")
      (l.join(fields) in FieldsRel.self.product(SymbolicSetRel.self) and
        ((f.join(l.join(fields)).lone and (f.join(l.join(fields)) in SymbolicSetRel.self)) forAll (f oneOf FieldsRel.self)) and
          ((l.join(fields).join(ss) in FieldsRel.self) forAll (ss oneOf SymbolicSetRel.self))
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
      (v.join(vals).one and (v.join(vals) in SymbolicSetRel.self)) forAll (v oneOf self) and
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
    lazy val typeOfSymTypeOfSetSubtyping = {
      val s = Variable.unary("s")
      val ss = Variable.unary("ss")
      val t = Variable.unary("t")
      val ts = Variable.unary("ts")
      ((s.join(typeOfSym) eq t) and (ss.join(typeOfSet) eq ts) and (s in ss.join(SymbolicSetRel.syms)) implies
        (ts in t.join(isSubType))) forAll
          ((s oneOf SymbolsRel.self) and (ss oneOf SymbolicSetRel.self) and (t oneOf self) and (ts oneOf self))
    }
    val typerels = defs.keys.map(c => (c,Relation.unary(s"Type$$${c.name}"))).toMap
  }

  def freshSymbolicSetRel(idopt: Option[Symbols]): (Relation, Formula) = {
    counter = counter + 1
    val ss = Relation.unary(s"ConcreteSymbolicSet$counter")
    val s = Variable.unary("s")
    val nameExpr = idopt.cata({ case id => IntConstant.constant(id).toExpression }, Expression.NONE)
    val nameConstraint = ((s.join(SymbolicSetRel.name) eq nameExpr) and
      idopt.cata(_ => s.join(TypesRel.typeOfSet) eq Expression.NONE, Formula.TRUE)) forAll (s oneOf ss)
    val subsetConstraint = (s in SymbolicSetRel.self) forAll (s oneOf ss)
    (ss, nameConstraint and subsetConstraint)
  }

  def staticConstraints : Formula = {
    SymbolsRel.nameTyping and SymbolsRel.nameUniqueness and SymbolsRel.locTyping and
    SymbolicSetRel.symsTyping and  SymbolicSetRel.nameTyping and SymbolicSetRel.nameUniqueness and
    LocsRel.nameTyping and LocsRel.nameUniqueness and
    FieldsRel.nameTyping and FieldsRel.nameUniqueness and
    VarsRel.nameTyping and VarsRel.nameUniqueness and VarsRel.valsTyping and
    TypesRel.typeOfLocTyping and TypesRel.typeOfSymTyping and TypesRel.typeOfSetTyping and
    TypesRel.isSubTypeTyping and TypesRel.typeOfSymTypeOfSetSubtyping and TypesRel.typeOfLocTypeOfSymEquality
  }

  def calculateBounds(setsymexprels : Set[Relation], setsymmap: Map[Symbols, Relation], symnames: Set[Integer], locs: Set[Loc], fieldmap: Map[String, Integer], varmap: Map[String, Integer]) : Bounds = {
    val locobjs = (locs ++ (100 to 150).map(Loc)).map(l => (Int.box(l.id), s"loc'${l.id}")).toMap
    val symbolids = symnames.map(i => (i, s"sym'$i")).toMap
    val symbolicsets = (for ((r, i) <- setsymexprels.zipWithIndex) yield (r, s"set'$i")).toMap
    val types = for ((c, _) <- TypesRel.typerels) yield (c, s"type'${c.name}")
    val fieldobjs = fieldmap.map { case (field, i) => (i, s"field'$field") }
    val varobjs = varmap.map { case (vr, i) => (i, s"var'$vr") }
    val setsymnames: Set[Integer] = setsymmap.keySet.map(s => Int.box(s))
    val atoms =  symbolids.keySet ++ symbolids.values ++ symbolicsets.values ++ setsymnames ++ types.values ++
      locobjs.keySet ++ locobjs.values ++ fieldobjs.keySet ++ fieldobjs.values ++ varobjs.keySet ++ varobjs.values
    val universe = new Universe(atoms.asJava)
    val bounds = new Bounds(universe)
    val f = universe.factory


    for (intval <- locobjs.keySet ++ symbolids.keySet ++ fieldobjs.keySet ++ varobjs.keySet)
      bounds.boundExactly(intval.intValue, f range (f tuple intval, f tuple intval))

    bounds.boundExactly(SymbolsRel.self, f setOf (symbolids.values.toSeq :_*))

    val symLocUpper = f noneOf 2
    for (symid <- symbolids.values.toSeq; locid <- locobjs.values.toSeq) symLocUpper.add((f tuple symid) product (f tuple locid))
    bounds.bound(SymbolsRel.loc, symLocUpper)

    for ((r, i) <- symbolicsets) bounds.boundExactly(r, f setOf i)
    bounds.boundExactly(SymbolicSetRel.self, f setOf (symbolicsets.values.toSeq :_*))

    for (setsymname <- setsymnames)
      bounds.boundExactly(setsymname.intValue, f range (f tuple setsymname, f tuple setsymname))

    bounds.boundExactly(VarsRel.self, f setOf (varobjs.values.toSeq :_*))
    val varnameUpper = f noneOf 2
    for ((varname, varid) <- varobjs) varnameUpper.add((f tuple varid) product (f tuple varname))
    bounds.boundExactly(VarsRel.name, varnameUpper)
    val varvalsUpper = f noneOf 2
    for (varid <- varobjs.values.toSeq; sset <- symbolicsets.values.toSeq) varvalsUpper.add((f tuple varid) product (f tuple sset))
    bounds.boundExactly(VarsRel.vals, varvalsUpper)

    bounds.boundExactly(FieldsRel.self, f setOf (fieldobjs.values.toSeq :_*))
    val fieldnameUpper = f noneOf 2
    for ((fieldname, fieldid) <- fieldobjs) fieldnameUpper.add((f tuple fieldid) product (f tuple fieldname))
    bounds.bound(FieldsRel.name, fieldnameUpper)

    val ssetrelsymsUpper = f noneOf 2
    for (symid <- symbolids.values.toSeq; sset <- symbolicsets.values.toSeq) ssetrelsymsUpper.add((f tuple sset) product (f tuple symid))
    bounds.bound(SymbolicSetRel.syms, ssetrelsymsUpper)
    val ssetrelnameUpper = f noneOf 2
    for ((ssym, rel) <- setsymmap) ssetrelnameUpper.add((f tuple symbolicsets(rel)) product (f tuple Int.box(ssym)))
    bounds.bound(SymbolicSetRel.name, ssetrelnameUpper)

    bounds.boundExactly(LocsRel.self, f setOf (locobjs.values.toSeq :_*))
    val locsnameUpper = f noneOf 2
    for ((locname, locid) <- locobjs) locsnameUpper.add((f tuple locid) product (f tuple locname))
    bounds.boundExactly(LocsRel.name, locsnameUpper)

    val symnameUpper = f noneOf 2
    for ((sname, sid) <- symbolids)
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
    for (ss <- symbolicsets.values.toSeq) {
      for (typ <- types.values.toSeq) {
        typeOfSetUpper.add((f tuple ss) product (f tuple typ))
      }
    }
    bounds.bound(TypesRel.typeOfSet, typeOfSetUpper)
    val typeOfSymUpper = f noneOf 2
    for (sid <- symbolids.values.toSeq) {
      for (typ <- types.values.toSeq) {
        typeOfSymUpper.add((f tuple sid) product (f tuple typ))
      }
    }
    bounds.bound(TypesRel.typeOfSym, typeOfSymUpper)
    val typeOfLocUpper = f noneOf 2
    for (lid <- locobjs.values.toSeq; typ <- types.values.toSeq) typeOfLocUpper.add((f tuple lid) product (f tuple typ))
    bounds.bound(TypesRel.typeOfLoc, typeOfLocUpper)
    bounds
  }

  def evalBoolExpr(b : BoolExpr[IsSymbolic.type], th : Map[Symbols, Relation], isNegated: Boolean = false)
  : String \/ EvalRes[Formula] = b match {
    case Eq(e1, e2) => evalBinaryBoolExpr(e1, _ eq _, e2, th, isNegated)
    case SetMem(e1, e2) => for {
        ee2 <- evalSetExpr(e2, th)
        (EvalState(rs2, is2, f2, th2), r2) = ee2
        formula = {
          val sym = Variable.unary("sym")
          val x = Variable.unary("x")
          val symInSyms = sym in x.join(SymbolicSetRel.syms)
          (e1 match {
            case Symbol(symident) => sym.join(SymbolsRel.name) eq IntConstant.constant(symident).toExpression
          }) implies (if (isNegated) symInSyms.not else symInSyms) forAll ((sym oneOf SymbolsRel.self) and (x oneOf r2))
        }
      } yield (EvalState(rs2, is2, formula and f2, th2), formula)
    case SetSubEq(e1, e2) =>  evalBinaryBoolExpr(e1, _ in _, e2, th, isNegated)
    case True() => (EvalState(Set[Relation](), Set[Integer](), Formula.TRUE, th), Formula.TRUE).right
    case And(b1,b2) =>
      for {
        eb1 <- evalBoolExpr(b1, th, isNegated)
        (EvalState(rs1, is1, fs1, th1), r1) = eb1
        eb2 <- evalBoolExpr(b2, th1, isNegated)
        (EvalState(rs2, is2, fs2, th2), r2) = eb2
      } yield (EvalState(rs1 union rs2, is1 union is2, fs1 and fs2, th2), if (isNegated) r1 or r2 else r1 and r2)
    case Not(b0) => for {
        eb <- evalBoolExpr(b0, th, !isNegated)
      } yield eb
  }

  def evalBinaryBoolExpr(e1: SetExpr[IsSymbolic.type], op: (Expression, Expression) => Formula, e2: SetExpr[IsSymbolic.type],
                         th: Map[Symbols, Relation], isNegated: Boolean): String \/ EvalRes[Formula] = {
    for {
      ee1 <- evalSetExpr(e1, th)
      (est1, r1) = ee1
      ee2 <- evalSetExpr(e2, est1.ssymmap)
      (est2, r2) = ee2
      formula = {
        val x1 = Variable.unary("x1")
        val x2 = Variable.unary("x2")
        val res = op(x1.join(SymbolicSetRel.syms), x2.join(SymbolicSetRel.syms))
        (if (isNegated) res.not else res) forAll ((x1 oneOf r1) and (x2 oneOf r2))
      }
    } yield (mergeEvalState(est1, est2), formula)
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
      (EvalState(Set(s), symbols.toSet, formula and nameConstraint, th), s).right
    case Part(syms) => ??? // TODO Implement
    case Union(e1, e2) =>
      evalBinarySetExpr(e1, _ union _, e2, th)
    case Diff(e1, e2) =>
      evalBinarySetExpr(e1, _ difference _, e2, th)
    case ISect(e1, e2) =>
      evalBinarySetExpr(e1, _ intersection _, e2, th)
    case SetSymbol(ident) =>
      if (th.contains(ident)) (EvalState(Set[Relation](), Set[Integer](), Formula.TRUE, th), th(ident)).right[String]
      else {
        val (s, nameConstraint) = freshSymbolicSetRel(ident.some)
        val formula = Formula.TRUE
        (EvalState(Set[Relation](s), Set[Integer](), formula and nameConstraint, th + (ident -> s)), s).right[String]
      }
  }

  def evalBinarySetExpr(e1: SetExpr[IsSymbolic.type], op: (Expression, Expression) => Expression, e2: SetExpr[IsSymbolic.type],
                        th : Map[Symbols, Relation]): String \/ EvalRes[Relation] = {
    for {
      ee1 <- evalSetExpr(e1,th)
      (EvalState(rs1, is1, f1, th1), r1) = ee1
      ee2 <- evalSetExpr(e2,th1)
      (EvalState(rs2, is2, f2, th2), r2) = ee2
      (s, nameConstraint) = freshSymbolicSetRel(none)
      formula = {
        val x = Variable.unary("x")
        val x1 = Variable.unary("x1")
        val x2 = Variable.unary("x2")
        x.join(SymbolicSetRel.syms) eq op(x1.join(SymbolicSetRel.syms),x2.join(SymbolicSetRel.syms)) forAll ((x oneOf s) and (x1 oneOf r1) and (x2 oneOf r2))
      }
    } yield (EvalState(Set(s) union rs1 union rs2, is1 union is2, formula and f1 and f2 and nameConstraint, th2), s)
  }

  def concretise(smem: SMem): String \/ CMem = {
    def extractConcreteMemory(instance: Instance): CMem = { println(instance); ??? }
    def cardConstraint(s: Variable, crd: Cardinality): Formula = crd match {
      case Single => s.join(SymbolicSetRel.syms).one
      case Many => Formula.TRUE
      case Opt => s.join(SymbolicSetRel.syms).lone
    }
    def createBidiMap[K,V](s: Seq[(K,V)]): (Map[K, V], Map[V,K]) = {
      (Map(s :_*), Map(s.map(_.swap) :_*))
    }
    val initEvalState = EvalState(Set(), Set(), Formula.TRUE, Map())
    val (varMapFrom, varMapTo) = createBidiMap(smem.stack.keySet.zipWithIndex.toSeq)
    val varevalres = smem.stack.foldLeft((initEvalState, Formula.TRUE).right[String]) { (str, vinfo) =>
      val (vr, exp) = vinfo
      for {
        st <- str
        (evalState, constraints) = st
        eexp <- evalSetExpr(exp, evalState.ssymmap)
        (EvalState(rs,is,f,th), setrel) = eexp
        varconstraint = {
          val v = Variable.unary("v")
          val ss = Variable.unary("ss")
          val valsConstraint = (v.join(VarsRel.name) eq IntConstant.constant(varMapFrom(vr)).toExpression) implies
                                   (v.join(VarsRel.vals) eq ss) forAll ((ss oneOf setrel) and (v oneOf VarsRel.self))
          valsConstraint
        }
      } yield (EvalState(evalState.ssymrels ++ rs, evalState.symnames ++ is, evalState.constraints and f, th), constraints and varconstraint)
    }
    val ssvconstraints = smem.heap.ssvltion.foldLeft(Formula.TRUE) { (constraints, ssinfo) =>
      val (ssym, ssdesc) = ssinfo
      val s = Variable.unary("s")
      val t = Variable.unary("t")
      (s.join(SymbolicSetRel.name) eq IntConstant.constant(ssym.id).toExpression implies
        (cardConstraint(s, ssdesc.crd) and (s.join(TypesRel.typeOfSet) eq t)) forAll
          ((s oneOf SymbolicSetRel.self) and (t oneOf TypesRel.typerels(ssdesc.cl)))) and constraints
    }
    val svconstraints = smem.heap.svltion.foldLeft(Formula.TRUE) { (constraints, sinfo) =>
      val (sym, sdesc) = sinfo
      (sdesc match {
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
            (s.join(TypesRel.typeOfSym) eq t)) forAll ((s oneOf SymbolsRel.self) and (t oneOf TypesRel.typerels(cl)))
      }) and constraints
    }
    val allFields = defs.childfields ++ defs.reffields
    val (fieldMapFrom, fieldMapTo) = createBidiMap(allFields.zipWithIndex.toSeq)
    def translateSpatial(initEvalState: EvalState) = smem.heap.initSpatial.foldLeft((initEvalState, Formula.TRUE).right[String]) { (st, locinfo) =>
      val (loc, sdesc) = locinfo
      val l = Variable.unary("l")
      val t = Variable.unary("t")
      val t2 = Variable.unary("t2")
      val typeConstraint = (l.join(LocsRel.name) eq IntConstant.constant(loc.id).toExpression) implies
        (l.join(TypesRel.typeOfLoc) eq t) and (t2 in TypesRel.typerels(sdesc.c)) and (sdesc.desctype match {
          case ExactDesc => t eq t2
          case AbstractDesc => t2 in t.join(TypesRel.isSubType)
          case PartialDesc(hasExact, possible) =>
            val exactConstraint = if (!hasExact) (t eq t2).not else Formula.TRUE
            val possibleConstraints = possible.foldLeft(Formula.FALSE) { (constraint,c) =>
              TypesRel.typerels(c) in t.join(TypesRel.isSubType) or constraint
            }
            (t2 in t.join(TypesRel.isSubType)) and exactConstraint and possibleConstraints
      }) `forSome` ((t oneOf TypesRel.self) and (t2 oneOf TypesRel.self)) forAll (l oneOf LocsRel.self)
      for {
        evalres <- st
        (evalstate, constraints) = evalres
        fieldEvalRes <- (sdesc.children ++ sdesc.refs).foldLeft((evalstate, Formula.TRUE).right[String]) { (st, fieldinfo) =>
          val (field, fieldval) = fieldinfo
          for {
            evalres <- st
            (evalstate, constraints) = evalres
            fieldvalres <- evalSetExpr(fieldval, evalstate.ssymmap)
            (fieldvalEvalState, fieldvalRel) = fieldvalres
            fieldconstraint = {
              val f = Variable.unary("f")
              val s = Variable.unary("s")
              (l.join(LocsRel.name) eq IntConstant.constant(loc.id).toExpression) and
                (f.join(FieldsRel.name) eq IntConstant.constant(fieldMapFrom(field)).toExpression) implies
                  (f.product(s) in l.join(LocsRel.fields)) forAll
                    ((l oneOf LocsRel.self) and (f oneOf FieldsRel.self) and (s oneOf fieldvalRel))
            }
          } yield (mergeEvalState(evalstate, fieldvalEvalState), constraints and fieldconstraint)
        }
        (fieldEvalState, fieldConstraints) = fieldEvalRes
      } yield (mergeEvalState(evalstate, fieldEvalState), constraints and typeConstraint and fieldConstraints)
    }
    val solver = new Solver
    solver.options.setSolver(SATFactory.DefaultSAT4J)
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
      allConstraints = staticConstraints and ssvconstraints and svconstraints and pureConstraints and spatialConstraints and est.constraints // and ...
      bounds = calculateBounds(est.ssymrels, est.ssymmap, est.symnames, smem.heap.initSpatial.keySet, fieldMapFrom.mapValues(Int.box), varMapFrom.mapValues(Int.box))
      solution = solver.solve(allConstraints, bounds)
      instance <- solution.outcome match {
        case Outcome.SATISFIABLE | Outcome.TRIVIALLY_SATISFIABLE =>
          val instance = solution.instance
          extractConcreteMemory (instance).right
        case Outcome.UNSATISFIABLE | Outcome.TRIVIALLY_UNSATISFIABLE => s"Unsatisfiable constraints: $allConstraints".left
      }
    } yield instance
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
      case UnknownLoc(cl, ownership, descendantpool) =>
        // TODO check consistency via SAT
        val newLoc = Loc(loccounter.++())
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
    }, Process(s"No such symbol: $sym".left))
  }

  def antialias(sym: Symbol, nheap: SHeap, loc: Loc): SHeap = {
    nheap.svltion.filter(_._2 == loc).keySet.foldLeft(nheap) { (stheap, sym2) => stheap.subst(sym2, sym) }
  }

  def unfoldFieldSet(loc: Loc, fieldSet: Map[Fields, (Class, Cardinality)], owned: Boolean): (SetSymbolValuation, Map[Fields, SetExpr[IsSymbolic.type]]) = {
    fieldSet.foldLeft((Map(): SetSymbolValuation, Map[Fields, SetExpr[IsSymbolic.type]]())) { (st, fieldkv) =>
      fieldkv match {
        case (f, (cl, crd)) =>
          val sym = SetSymbol(symcounter.++())
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
           nc <- EitherT.right[Process0,String,Class](Process.emitAll(dt.possible.toSeq))
           cd <- EitherT[Process0, String, ClassDefinition](defs.get(nc).cata(_.right, s"No such class: ${nc.name}".left).point[Process0])
           (psdesc, nheap) = unfoldAbstract(SpatialDesc(c, AbstractDesc, children, refs, descendantpool), cd, heap)
           res <- EitherT[Process0, String, (SpatialDesc, SHeap)](
                  if (containsTargetField(psdesc)) (psdesc, nheap).right.point[Process0]
                  else unfoldPartial(psdesc.c, psdesc.desctype.asInstanceOf[PartialDesc], psdesc.children, psdesc.refs, psdesc.descendantpools, nheap))
        } yield res).run
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
