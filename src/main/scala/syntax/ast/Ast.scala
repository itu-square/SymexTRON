package syntax.ast

import monocle.{POptional, Lens, PLens, Iso}
import monocle.macros.{GenIso, GenLens, GenPrism}
import language.higherKinds
import scalaz.\/

case class Class(name: String) // To be defined later

sealed trait Cardinality { def isOptional: Boolean }
case class Single() extends Cardinality {
  def isOptional = false
}
case class Many() extends Cardinality {
  def isOptional = true
}
case class Opt() extends Cardinality {
  def isOptional = true
}

case class ClassDefinition(name: String, children: Map[Fields, (Class, Cardinality)],
                           refs: Map[Fields, (Class, Cardinality)], supers: Class*)

sealed trait BasicExpr
case class Symbol(id: Symbols) extends BasicExpr
case class Var(name: Vars) extends BasicExpr

sealed trait SetExpr
case class SetLit(es: BasicExpr*) extends SetExpr
case class Union(e1 : SetExpr, e2 : SetExpr) extends SetExpr
case class Diff(e1 : SetExpr, e2 : SetExpr) extends SetExpr
case class ISect(e1 : SetExpr, e2 : SetExpr) extends SetExpr
case class SetVar(name: Vars) extends SetExpr
case class SetSymbol(id: Symbols) extends SetExpr

sealed trait BoolExpr
case class Eq(e1: SetExpr, e2: SetExpr) extends BoolExpr
case class ClassMem(e1: SetExpr, s: Class) extends BoolExpr
case class SetMem(e1: BasicExpr, e2: SetExpr) extends BoolExpr
case class SetSub(e1: SetExpr, e2: SetExpr) extends BoolExpr
case class SetSubEq(e1: SetExpr, e2: SetExpr) extends BoolExpr
case class And(bs: BoolExpr*) extends BoolExpr
case class Not(b: BoolExpr) extends BoolExpr

sealed trait MatchExpr
case class MSet(e : SetExpr) extends MatchExpr
case class Match(e : SetExpr, c : Class) extends MatchExpr
case class MatchStar(e : SetExpr, c : Class) extends MatchExpr

object MatchExpr {
  val _me_e = Lens[MatchExpr, SetExpr]({
      case MSet(e) => e
      case Match(e, c) => e
      case MatchStar(e, c) => e
    })(newe => {
      case MSet(e) => MSet(newe)
      case Match(e, c) => Match(newe, c)
      case MatchStar(e, c) => MatchStar(newe, c)
    })
}

sealed abstract class SpatialDesc
case class AbstractDesc(c : Class, unowned : SetExpr) extends SpatialDesc
case class ConcreteDesc(c : Class, children : Map[Fields, SetExpr], refs : Map[Fields, SetExpr]) extends SpatialDesc

object SpatialDesc {
  val _sd_abstract = GenPrism[SpatialDesc, AbstractDesc]
  val _sd_concrete = GenPrism[SpatialDesc, ConcreteDesc]
  val _sd_c = Lens[SpatialDesc, Class]({ case ConcreteDesc(c, _, _) => c case AbstractDesc(c, _) => c })(newc => {
    case ConcreteDesc(oldc, chld, refs) => ConcreteDesc(newc, chld, refs)
    case AbstractDesc(oldc, unowned) => AbstractDesc(newc, unowned)
  })
}

object AbstractDesc {
  val _ad_c = GenLens[AbstractDesc](_.c)
  val _ad_unowned = GenLens[AbstractDesc](_.unowned)
}

object ConcreteDesc {
  val _cd_c = GenLens[ConcreteDesc](_.c)
  val _cd_children = GenLens[ConcreteDesc](_.children)
  val _cd_refs = GenLens[ConcreteDesc](_.refs)
}

case class QSpatial(e : SetExpr, c : Class, unowned : SetExpr)

object QSpatial {
  val _qs_e = GenLens[QSpatial](_.e)
  val _qs_c = GenLens[QSpatial](_.c)
  val _qs_unowned = GenLens[QSpatial](_.unowned)
}

case class SHeap(spatial: Spatial[Symbols], qspatial: Set[QSpatial], pure : Prop)

object SHeap {
  val _sh_spatial  = GenLens[SHeap](_.spatial)
  val _sh_qspatial = GenLens[SHeap](_.qspatial)
  val _sh_pure     = GenLens[SHeap](_.pure)
}

case class SMem(stack: SStack, heap: SHeap)

object SMem {
  val _sm_stack = GenLens[SMem](_.stack)
  val _sm_heap = GenLens[SMem](_.heap)
}

sealed trait Statement
case class StmtSeq(ss : Statement*) extends Statement
case class AssignVar(x : Vars, e : SetExpr) extends Statement
case class LoadField(x : Vars, e : SetExpr, f : Fields) extends Statement
case class New(x : Vars, c : Class) extends Statement
case class AssignField(e1 : SetExpr, f : Fields, e2 : SetExpr) extends Statement
case class If(cs : (BoolExpr, Statement)*) extends Statement
case class For(x: Vars, m: MatchExpr, sb: Statement)
  extends Statement
case class Fix(e : SetExpr, sb: Statement) extends Statement
