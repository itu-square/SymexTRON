package syntax.ast

import helper._

case class Sort(name: String) // To be defined later

class SortDefinition(val name: String, val children: Map[Fields, Sort], val refs: Map[Fields, Sort], supers: Sort*)

sealed trait Expr
sealed trait BasicExpr extends Expr
case class Symbol(id: Symbols) extends BasicExpr
case class Var(name: Vars) extends BasicExpr
case class SetE(es: BasicExpr*) extends Expr
case class Union(e1 : Expr, e2 : Expr) extends Expr
case class Diff(e1 : Expr, e2 : Expr) extends Expr
case class ISect(e1 : Expr, e2 : Expr) extends Expr

sealed trait SimpleProp

case class Eq(e1: Expr, e2: Expr) extends SimpleProp
case class SortMem(e1: Expr, s: Sort) extends SimpleProp
case class SetMem(e1: BasicExpr, e2: Expr) extends SimpleProp
case class SetSub(e1: Expr, e2: Expr) extends SimpleProp
case class SetSubEq(e1: Expr, e2: Expr) extends SimpleProp
case class Not(p: SimpleProp) extends SimpleProp

sealed trait Pred
case class Descendant(s : Sort, e1 : Expr, e2 : Expr) extends Pred
case class NotDescendant(e1 : Expr, e2 : Expr) extends Pred
case class Def(s : Sort, e : Expr) extends Pred

case class SymbolicHeap(pure : Prop, spatial : Spatial, preds: Set[Pred])

case class SymbolicMemory(stack: SymbolicStack, heap: SymbolicHeap)

sealed trait Command
case class Fail() extends Command
case class CSeq(cs : Command*) extends Command
case class AssignVar(x : Vars, e : Expr) extends Command
case class LoadField(x : Vars, e : Expr, f : Fields) extends Command
case class New(x : Vars, s : Sort) extends Command
case class AssignField(e1 : Expr, f : Fields, e2 : Expr) extends Command
case class If(cs : Set[(SimpleProp, Command)]) extends Command
case class For(x : Vars, s : Sort, e : Expr, inv: (Symbols, Set[SymbolicMemory]), cb: Command)
  extends Command
case class ForMatch(x : Vars, s : Sort, e : Expr, inv: (Symbols, Set[SymbolicMemory]), cb: Command)
  extends Command
case class Fix(e : Expr, inv: (Symbols, Set[SymbolicMemory]), cb: Command) extends Command

sealed trait OwnerInfo
case class Unowned() extends OwnerInfo
case class Owned(owner : Symbol, f : Fields) extends OwnerInfo
