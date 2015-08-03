package syntax.ast

case class Sort() // To be defined later

sealed trait Expr
case class Nil() extends Expr
case class Var(name: Vars) extends Expr

sealed trait SimpleProp {
  def sym: SimpleProp
}

case class Eq(e1: Expr, e2: Expr) extends SimpleProp {
  override def sym: Eq = Eq(e2, e1)
}
case class Not(e : Eq) extends SimpleProp {
  override def sym: Not = Not(e.sym)
}

case class SymbolicHeap(pi : Prop, sig : Spatial)

sealed trait Command
case class Skip() extends Command
case class AssignVar(x : Vars, e : Expr, c : Command) extends Command
case class HeapLookup(x : Vars, e : Expr, f : Fields, c : Command) extends Command
case class HeapMutate(e1 : Expr, f : Fields, e2 : Expr, c : Command) extends Command
case class New(x : Vars, s : Sort, c : Command) extends Command
case class If(p : SimpleProp, ct : Command, ce : Command, c : Command) extends Command

// Smart constructor
object Accesses {
  def unapply(c : Command): Option[Expr] = {
    c match {
      case HeapLookup(x, e, f, c) => Some(e)
      case HeapMutate(e1, f, e2, c) => Some(e1)
      case _ => None
    }
  }
}