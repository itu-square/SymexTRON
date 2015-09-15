package syntax.ast

import helper._

case class Sort(name: String) // To be defined later

class SortDefinition(val name: String, val children: Map[Fields, Sort], val refs: Map[Fields, Sort], supers: Sort*)

sealed trait BasicExpr
case class Symbol(id: Symbols) extends BasicExpr
case class Var(name: Vars) extends BasicExpr

sealed trait SetExpr
case class SetLit(es: BasicExpr*) extends SetExpr
case class Union(e1 : SetExpr, e2 : SetExpr) extends SetExpr
case class Diff(e1 : SetExpr, e2 : SetExpr) extends SetExpr
case class ISect(e1 : SetExpr, e2 : SetExpr) extends SetExpr
case class Match(e : SetExpr, s : Sort) extends SetExpr
case class MatchStar(e : SetExpr, s : Sort) extends SetExpr
case class SetVar(name: Vars) extends SetExpr
case class SetSymbol(id: Symbols) extends SetExpr

sealed trait BoolExpr
case class Eq(e1: SetExpr, e2: SetExpr) extends BoolExpr
case class SortMem(e1: SetExpr, s: Sort) extends BoolExpr
case class SetMem(e1: BasicExpr, e2: SetExpr) extends BoolExpr
case class SetSub(e1: SetExpr, e2: SetExpr) extends BoolExpr
case class SetSubEq(e1: SetExpr, e2: SetExpr) extends BoolExpr
case class Not(p: BoolExpr) extends BoolExpr


sealed trait Pred
case class Descendant(s : Sort, e1 : SetExpr, e2 : SetExpr) extends Pred
case class NotDescendant(e1 : SetExpr, e2 : SetExpr) extends Pred
case class Def(s : Sort, e : SetExpr) extends Pred

case class SymbolicHeap(pure : Prop, spatial : Spatial, preds: Set[Pred])

case class SymbolicMemory(stack: SymbolicStack, heap: SymbolicHeap)

sealed trait Command
case class Fail() extends Command
case class CSeq(cs : Command*) extends Command
case class AssignVar(x : Vars, e : SetExpr) extends Command
case class LoadField(x : Vars, e : SetExpr, f : Fields) extends Command
case class New(x : Vars, s : Sort) extends Command
case class AssignField(e1 : SetExpr, f : Fields, e2 : SetExpr) extends Command
case class If(cs : Set[(BoolExpr, Command)]) extends Command
case class For(x : Vars, s : Sort, e : SetExpr, inv: (Symbols, Set[SymbolicMemory]), cb: Command)
  extends Command
case class Fix(e : SetExpr, inv: (Symbols, Set[SymbolicMemory]), cb: Command) extends Command

sealed trait OwnerInfo
case class Unowned() extends OwnerInfo
case class Owned(owner : Symbol, f : Fields) extends OwnerInfo

