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

  implicit class SubstOwnerInfo(o : OwnerInfo) extends Subst[OwnerInfo] {
    override def subst(x: SetSymbol, e: SetExpr): OwnerInfo = o match {
      case Unowned() => Unowned()
      case Owned(owner, f) => Owned(owner.subst(x, e).asInstanceOf, f)
    }

    override def subst(x: Symbol, e: BasicExpr): OwnerInfo = o match {
      case Unowned() => Unowned()
      case Owned(owner, f) =>  Owned(owner.subst(x, e).asInstanceOf, f)
    }
  }

  implicit class SubstSpatial(sig: Spatial) extends Subst[Spatial] {
    override def subst(x: SetSymbol, e: SetExpr): Spatial = sig.map({
      (e0 : SetExpr, fss : Set[(Map[Fields, SetExpr], OwnerInfo)]) =>
        (e0.subst(x, e), fss.map({
          (fs : Map[Fields, SetExpr], owninfo : OwnerInfo) => {
            val fs_ = fs.mapValues(_.subst(x, e))
            (fs_, owninfo.subst(x, e))
          }
        }.tupled))
    }.tupled)

    override def subst(x: Symbol, e: BasicExpr): Spatial = sig.map({
      (e0 : SetExpr, fss : Set[(Map[Fields, SetExpr], OwnerInfo)]) =>
        (e0.subst(x, e), fss.map({
          (fs : Map[Fields, SetExpr], owninfo : OwnerInfo) => {
            val fs_ = fs.mapValues(_.subst(x, e))
            (fs_, owninfo.subst(x, e))
          }
        }.tupled))
    }.tupled)
  }

  implicit class SubstPred(p : Pred) extends Subst[Pred] {
    override def subst(x: SetSymbol, e: SetExpr): Pred = p match {
      case Descendant(s, e1, e2) => Descendant(s, e1.subst(x, e), e2.subst(x, e))
      case NotDescendant(e1, e2) => NotDescendant(e1.subst(x, e), e2.subst(x, e))
      case Def(s, e1) => Def(s, e1.subst(x, e))
    }

    override def subst(x: Symbol, e: BasicExpr): Pred = p match {
      case Descendant(s, e1, e2) => Descendant(s, e1.subst(x, e), e2.subst(x, e))
      case NotDescendant(e1, e2) => NotDescendant(e1.subst(x, e), e2.subst(x, e))
      case Def(s, e1) => Def(s, e1.subst(x, e))
    }
  }

  implicit class SubstSymbolicHeap(h: SHeap) extends Subst[SHeap] {
    override def subst(x: SetSymbol, e: SetExpr): SHeap = h match {
      case SHeap(pi, sig, preds) => SHeap(pi.subst(x, e), sig.subst(x, e), preds.map(_.subst(x, e)))
    }

    override def subst(x: Symbol, e: BasicExpr): SHeap = h match {
      case SHeap(pi, sig, preds) => SHeap(pi.subst(x, e), sig.subst(x, e), preds.map(_.subst(x, e)))
    }
  }

  implicit class SubstSymbolicMemory(m : SMem) extends Subst[SMem] {
    override def subst(x: SetSymbol, e: SetExpr): SMem = SMem(m.stack, m.heap.subst(x, e))
    override def subst(x: Symbol, e: BasicExpr): SMem = SMem(m.stack, m.heap.subst(x, e))
  }
}
