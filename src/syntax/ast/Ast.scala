package syntax.ast

case class Sort(name: String) // To be defined later

class SortDefinition(name: String, children: Map[Fields, Sort], fields: Map[Fields, Sort])

sealed trait Expr
case class Nil() extends Expr
case class Symbol(id: Symbols) extends Expr

sealed trait SimpleProp {
  def sym: SimpleProp
}

case class Eq(e1: Expr, e2: Expr) extends SimpleProp {
  override def sym: Eq = Eq(e2, e1)
}
case class NotEq(e1: Expr, e2: Expr) extends SimpleProp {
  override def sym: NotEq = NotEq(e2, e1)
}

case class SymbolicHeap(pure : Prop, spatial : Spatial)

case class SymbolicMemory(stack: Stacks, heap: SymbolicHeap)

sealed trait Command
case class Skip() extends Command
case class Fail() extends Command
case class AssignVar(x : Vars, e : Expr, c : Command) extends Command
case class Load(x : Vars, e : Expr, f : Fields, c : Command) extends Command
case class New(x : Vars, s : Sort, c : Command) extends Command
case class AssignRef(e1 : Expr, f : Fields, e2 : Expr, c : Command) extends Command
case class AssignChild(e1 : Expr, f : Fields, e2 : Expr, c : Command) extends Command
case class If(p : SimpleProp, cs : Set[(Expr, Command)], c : Command) extends Command
case class For(x : Vars, s : Sort, e : Expr, inv: (Symbols, Set[SymbolicMemory]), cb: Command, c: Command)
  extends Command
case class ForMatch(x : Vars, s : Sort, e : Expr, inv: (Symbols, Set[SymbolicMemory]), cb: Command, c: Command)
  extends Command
case class Fix(e : Expr, inv: (Symbols, Set[SymbolicMemory]), cb: Command, c : Command)
