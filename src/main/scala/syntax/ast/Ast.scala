package syntax.ast

import helper._

case class Class(name: String) // To be defined later

class ClassDefinition(val name: String, val children: Map[Fields, Class], val refs: Map[Fields, Class], supers: Class*)

sealed trait BasicExpr
case class Symbol(id: Symbols) extends BasicExpr
case class Var(name: Vars) extends BasicExpr

sealed trait SetExpr

sealed trait BoolExpr

case class SetLit(es: BasicExpr*) extends SetExpr
case class Union(e1 : SetExpr, e2 : SetExpr) extends SetExpr
case class Diff(e1 : SetExpr, e2 : SetExpr) extends SetExpr
case class ISect(e1 : SetExpr, e2 : SetExpr) extends SetExpr
case class SetVar(name: Vars) extends SetExpr
case class SetSymbol(id: Symbols) extends SetExpr
case class GuardedSet(e1 : SetExpr, guard: BoolExpr) extends SetExpr

case class Eq(e1: SetExpr, e2: SetExpr) extends BoolExpr
case class ClassMem(e1: SetExpr, s: Class) extends BoolExpr
case class SetMem(e1: BasicExpr, e2: SetExpr) extends BoolExpr
case class SetSub(e1: SetExpr, e2: SetExpr) extends BoolExpr
case class SetSubEq(e1: SetExpr, e2: SetExpr) extends BoolExpr
case class Not(p: BoolExpr) extends BoolExpr

sealed trait MatchExpr
case class MSet(e : SetExpr) extends MatchExpr
case class Match(e : SetExpr, c : Class) extends MatchExpr
case class MatchStar(e : SetExpr, c : Class) extends MatchExpr

sealed trait SpatialDesc

case class SHeap(spatial: Map[Symbol, SpatialDesc], pure : Prop)

case class SMem(stack: SStack, heap: SHeap)

sealed trait Statement
case class StmtSeq(ss : Statement*) extends Statement
case class AssignVar(x : Vars, e : SetExpr) extends Statement
case class LoadField(x : Vars, e : SetExpr, f : Fields) extends Statement
case class New(x : Vars, c : Class) extends Statement
case class AssignField(e1 : SetExpr, f : Fields, e2 : SetExpr) extends Statement
case class If(cs : Set[(BoolExpr, Statement)]) extends Statement
case class For(x : Vars, c : Class, m : MatchExpr, sb: Statement)
  extends Statement
case class Fix(e : SetExpr, sb: Statement) extends Statement

