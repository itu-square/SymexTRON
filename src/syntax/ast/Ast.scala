package syntax.ast

case class Sort() // To be defined later

sealed trait Expr
case class Nil() extends Expr
case class Var(name: Vars) extends Expr

// Perhaps convert to a set of equalities
sealed trait Prop
case class True() extends Prop
case class And(p1 : Prop, p2 : Prop) extends Prop
sealed trait SimpleProp extends Prop
case class Eq(e1: Expr, e2: Expr) extends SimpleProp
case class Not(e : SimpleProp) extends SimpleProp

// Perhaps convert to a multimap (optionally with a set of predicates later)
sealed trait Spatial
case class Empty() extends Spatial
case class Inst(e : Expr, l : Map[Fields, Expr]) extends Spatial
case class Sep(sig1 : Spatial, sig2 : Spatial) extends Spatial

case class SymbolicHeap(pi : Prop, sig : Spatial)

sealed trait Command
case class Skip() extends Command
case class AssignVar(x : Vars, e : Expr, c : Command) extends Command
case class HeapLookup(x : Vars, e : Expr, f : Fields, c : Command) extends Command
case class HeapMutate(e1 : Expr, f : Fields, e2 : Expr, c : Command) extends Command
case class New(x : Var, s : Sort, c : Command) extends Command
case class If(p : SimpleProp, ct : Command, ce : Command, c : Command)

