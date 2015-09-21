package semantics

import syntax.ast._

trait Subst[+T] {
  def subst(x : Symbol,    e : BasicExpr) : T
  def subst(x : SetSymbol, e : SetExpr)   : T
}

object Subst {

  implicit class SubstBasicExpr(e0: BasicExpr) extends Subst[BasicExpr] {
    override def subst(x: SetSymbol, e1: SetExpr): BasicExpr = identity(e0)
    override def subst(x: Symbol, e1: BasicExpr): BasicExpr = e0 match {
      case Var(name) => Var(name)
      case Symbol(id) if id == x.id => e1
      case Symbol(id) => Symbol(id)
    }
  }

  implicit class SubstExpr(e0: SetExpr) extends Subst[SetExpr] {
    override def subst(x: SetSymbol, e: SetExpr): SetExpr = e0 match {
      case SetLit(es@_*) => SetLit(es :_*)
      case Union(e1, e2) => Union(e1.subst(x, e), e2.subst(x, e))
      case Diff(e1, e2) => Diff(e1.subst(x, e), e2.subst(x, e))
      case ISect(e1, e2) => ISect(e1.subst(x, e), e2.subst(x, e))
      case GuardedSet(e1, guard) => GuardedSet(e1.subst(x, e), guard.subst(x, e))
      case SetVar(name) => SetVar(name)
      case SetSymbol(id) if id == x.id => e
      case SetSymbol(id) => SetSymbol(id)
    }

    override def subst(x: Symbol, e: BasicExpr): SetExpr = e0 match {
      case SetLit(es@_*) => SetLit(es.map(_.subst(x, e)) :_*)
      case Union(e1, e2) => Union(e1.subst(x, e), e2.subst(x, e))
      case Diff(e1, e2) => Diff(e1.subst(x, e), e2.subst(x, e))
      case ISect(e1, e2) => ISect(e1.subst(x, e), e2.subst(x, e))
      case GuardedSet(e1, guard) => GuardedSet(e1.subst(x, e), guard.subst(x, e))
      case SetVar(name) => SetVar(name)
      case SetSymbol(id) => SetSymbol(id)
    }
  }

  implicit class SubstBoolExpr(p: BoolExpr) extends Subst[BoolExpr] {
    override def subst(x: SetSymbol, e: SetExpr): BoolExpr = p match {
      case Eq(e1, e2) => Eq(e1.subst(x, e), e2.subst(x, e))
      case ClassMem(e1, s) => ClassMem(e1.subst(x, e), s)
      case SetMem(e1, e2) =>
        val ee2 = e2.subst(x, e)
        SetMem(e1, ee2)
      case SetSub(e1, e2) => SetSub(e1.subst(x, e), e2.subst(x, e))
      case SetSubEq(e1, e2) => SetSubEq(e1.subst(x, e), e2.subst(x, e))
      case Not(pp) => Not(pp.subst(x,e))
    }

    override def subst(x: Symbol, e: BasicExpr): BoolExpr = p match {
      case Eq(e1, e2) => Eq(e1.subst(x, e), e2.subst(x, e))
      case ClassMem(e1, s) => ClassMem(e1.subst(x, e), s)
      case SetMem(e1, e2) =>
        val ee2 = e2.subst(x, e)
        SetMem(e1, ee2)
      case SetSub(e1, e2) => SetSub(e1.subst(x, e), e2.subst(x, e))
      case SetSubEq(e1, e2) => SetSubEq(e1.subst(x, e), e2.subst(x, e))
      case Not(pp) => Not(pp.subst(x,e))
    }
  }

  implicit class SubstProp(pi: Prop) extends Subst[Prop] {
    override def subst(x: SetSymbol, e: SetExpr): Prop = pi.map(_.subst(x, e))
    override def subst(x : Symbol, e: BasicExpr): Prop = pi.map(_.subst(x, e))
  }
}
