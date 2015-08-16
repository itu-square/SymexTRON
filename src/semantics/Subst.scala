package semantics

import syntax.ast._

trait Subst[T] {
  def subst(x : Vars, e : Expr) : T
}

object Subst {
  implicit class SubstExpr(e0 : Expr) extends Subst[Expr] {
    override def subst(x: Vars, e1: Expr): Expr = e0 match {
      case Symbol(name) if name == x => e1
      case _ => e0
    }
  }

  implicit class SubstSimpleProp(p : SimpleProp) extends Subst[SimpleProp] {
    override def subst(x: Vars, e: Expr): SimpleProp = p match {
      case Eq(e1, e2) => Eq(e1.subst(x, e), e2.subst(x, e))
      case Not(e1) => not(e1.subst(x, e))
    }
  }

  implicit class SubstProp(pi : Prop) extends Subst[Prop] {
    override def subst(x: Vars, e: Expr): Prop = pi.map(_.subst(x, e))
  }

  implicit class SubstSpatial(sig : Spatial) extends Subst[Spatial] {
    override def subst(x: Vars, e: Expr): Spatial = sig.mapValues(_.map(_.mapValues(_.subst(x, e))))
  }

  implicit class SubstSymbolicHeap(h : SymbolicHeap) extends Subst[SymbolicHeap] {
    override def subst(x: Vars, e: Expr): SymbolicHeap = h match {
      case SymbolicHeap(pi, sig) => SymbolicHeap(pi.subst(x, e), sig.subst(x, e))
    }
  }
}