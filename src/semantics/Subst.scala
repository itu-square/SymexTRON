package semantics

import syntax.ast._

trait Subst[T] {
  def subst(x : Vars, e : Expr) : T
}

object Subst {
  implicit class SubstExpr(e0 : Expr) extends Subst[Expr] {
    override def subst(x: Vars, e1: Expr): Expr = e0 match {
      case Var(name) if name == x => e1
      case _ => e0
    }
  }

  implicit class SubstProp(pi : Prop) extends Subst[Prop] {
    override def subst(x: Vars, e: Expr): Prop = pi match {
      case True() => True()
      case And(p1, p2) => And(p1.subst(x, e), p2.subst(x, e))
      case Eq(e1, e2) => Eq(e1.subst(x, e), e2.subst(x, e))
      case Not(e1) => Not(e1.subst(x, e).asInstanceOf[SimpleProp]) //Cast should be safe
    }
  }

  implicit class SubstSpatial(sig : Spatial) extends Subst[Spatial] {
    override def subst(x: Vars, e: Expr): Spatial = sig match {
      case Empty() => Empty()
      case Inst(e1, l) => Inst(e1.subst(x, e), l.mapValues(ei => ei.subst(x, e)))
      case Sep(sig1, sig2) => Sep(sig1.subst(x, e), sig2.subst(x, e))
    }
  }

  implicit class SubstSymbolicHeap(h : SymbolicHeap) extends Subst[SymbolicHeap] {
    override def subst(x: Vars, e: Expr): SymbolicHeap = h match {
      case SymbolicHeap(pi, sig) => SymbolicHeap(pi.subst(x, e), sig.subst(x, e))
    }
  }
}