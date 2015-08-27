package semantics

import syntax.ast._

trait Subst[T] {
  def subst(x : Symbol, e : BasicExpr) : T
}

sealed trait Foo
case class Bar(foos : Foo*) extends Foo

object Test {
  def matchit(f : Foo) = f match {
    case Bar(foos @ _*) =>
  }
}

object Subst {

  implicit class SubstBasicExpr(e0: BasicExpr) extends Subst[BasicExpr] {
    override def subst(x: Symbol, e1: BasicExpr): BasicExpr = e0 match {
      case Var(name) => Var(name)
      case Symbol(ident) if ident == x.id => e1
      case Symbol(ident) => Symbol(ident)
    }
  }

  implicit class SubstExpr(e0: Expr) extends Subst[Expr] {
    override def subst(x: Symbol, e: BasicExpr): Expr = e0 match {
      case e0: BasicExpr => e.subst(x, e)
      case SetE(es@_*) => SetE(es.map(_.subst(x, e)) : _*)
      case Union(e1, e2) => Union(e1.subst(x, e), e2.subst(x, e))
      case Diff(e1, e2) => Diff(e1.subst(x, e), e2.subst(x, e))
      case ISect(e1, e2) => ISect(e1.subst(x, e), e2.subst(x, e))
    }
  }

  implicit class SubstSimpleProp(p: SimpleProp) extends Subst[SimpleProp] {
    override def subst(x: Symbol, e: BasicExpr): SimpleProp = p match {
      case Eq(e1, e2) => Eq(e1.subst(x, e), e2.subst(x, e))
      case SortMem(e1, s) => SortMem(e1.subst(x, e), s)
      case SetMem(e1, e2) => SetMem(e1.subst(x, e), e2.subst(x, e))
      case SetSub(e1, e2) => SetSub(e1.subst(x, e), e2.subst(x, e))
      case SetSubEq(e1, e2) => SetSubEq(e1.subst(x, e), e2.subst(x, e))
      case Not(p) => Not(p.subst(x,e))
    }
  }

  implicit class SubstProp(pi: Prop) extends Subst[Prop] {
    override def subst(x: Symbol, e: BasicExpr): Prop = pi.map(_.subst(x, e))
  }

  implicit class SubstOwnerInfo(o : OwnerInfo) extends Subst[OwnerInfo] {
    override def subst(x: Symbol, e: BasicExpr): OwnerInfo = o match {
      case Unowned() => Unowned()
      case Owned(owner, f) => Owned(owner.subst(x, e).asInstanceOf, f)
    }
  }

  implicit class SubstSpatial(sig: Spatial) extends Subst[Spatial] {
    override def subst(x: Symbol, e: BasicExpr): Spatial = sig.map({
      (e0 : Expr, fss : Set[(Map[Fields, Expr], OwnerInfo)]) =>
        (e0.subst(x, e), fss.map({
          (fs : Map[Fields, Expr], owninfo : OwnerInfo) => {
            val fs_ = fs.mapValues(_.subst(x, e))
            (fs_, owninfo.subst(x, e))
          }
        }.tupled))
    }.tupled)
  }

  implicit class SubstPred(p : Pred) extends Subst[Pred] {
    override def subst(x: Symbol, e: BasicExpr): Pred = p match {
      case Descendant(s, e1, e2) => Descendant(s, e1.subst(x, e), e2.subst(x, e))
      case NotDescendant(e1, e2) => NotDescendant(e1.subst(x, e), e2.subst(x, e))
      case Def(s, e1) => Def(s, e1.subst(x, e))
    }
  }

  implicit class SubstSymbolicHeap(h: SymbolicHeap) extends Subst[SymbolicHeap] {
    override def subst(x: Symbol, e: BasicExpr): SymbolicHeap = h match {
      case SymbolicHeap(pi, sig, preds) => SymbolicHeap(pi.subst(x, e), sig.subst(x, e), preds.map(_.subst(x, e)))
    }
  }
}
