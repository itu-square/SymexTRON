package semantics

import syntax.ast._

trait FreeVariables[T] {
  def freevars : Set[Vars]
}

object FreeVariables {
  implicit class FreeVariablesExpr(e : Expr) extends FreeVariables[Expr] {
    override def freevars: Set[Vars] = e match {
      case Nil() => Set()
      case Var(name) => Set(name)
    }
  }

  implicit class FreeVariablesSimpleProp(p : SimpleProp) extends FreeVariables[SimpleProp] {
    override def freevars: Set[Vars] = p match {
      case Eq(e1, e2) => e1.freevars ++ e2.freevars
      case Not(e) => e.freevars
    }
  }

  implicit class FreeVariablesProp(pi : Prop) extends FreeVariables[Prop] {
    override def freevars: Set[Vars] = pi.flatMap(_.freevars)
  }

  implicit class FreeVariablesSpatial(sig : Spatial) extends FreeVariables[Spatial] {
    override def freevars: Set[Vars] = sig.values.flatMap(_.flatMap(_.values.flatMap(_.freevars))).toSet
  }

  implicit class FreeVariablesSymbolicHeap(h : SymbolicHeap) extends FreeVariables[SymbolicHeap] {
    override def freevars: Set[Vars] = h.pi.freevars ++ h.sig.freevars
  }
}
