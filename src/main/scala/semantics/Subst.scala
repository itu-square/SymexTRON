package semantics

import syntax.ast.QSpatial._
import syntax.ast._

trait Subst[T] {
  def toT : T

  def subst(x : Symbols, e : BasicExpr) : T
  def subst(x : Symbols, e : SetExpr)   : T
  def subst_all[B <: BasicExpr](th : Map[Symbols, B])(implicit fromT: T => Subst[T]) : T =
    th.foldLeft(toT)((t : T, kv : (Symbols, B)) => t.subst(kv._1, kv._2))
  def subst_all[S <: SetExpr](th : Map[Symbols, S])(implicit fromT: T => Subst[T], dummy: DummyImplicit) : T =
    th.foldLeft(toT)((t : T, kv : (Symbols, S)) => t.subst(kv._1, kv._2))
}

object Subst {

  implicit class SubstBasicExpr(e0: BasicExpr) extends Subst[BasicExpr] {
    override def toT = e0

    override def subst(x: Symbols, e1: SetExpr): BasicExpr = e0
    override def subst(x: Symbols, e1: BasicExpr): BasicExpr = e0 match {
      case Symbol(id) if id == x => e1
      case _ => e0
    }
  }

  implicit class SubstExpr(e0: SetExpr) extends Subst[SetExpr] {
    override def toT = e0

    override def subst(x: Symbols, e: SetExpr): SetExpr = e0 match {
      case SetLit(es@_*) => SetLit(es :_*)
      case Union(e1, e2) => Union(e1.subst(x, e), e2.subst(x, e))
      case Diff(e1, e2) => Diff(e1.subst(x, e), e2.subst(x, e))
      case ISect(e1, e2) => ISect(e1.subst(x, e), e2.subst(x, e))
      case SetVar(name) => SetVar(name)
      case SetSymbol(_,id) if id == x => e
      case SetSymbol(c, id) => SetSymbol(c, id)
    }

    override def subst(x: Symbols, e: BasicExpr): SetExpr = e0 match {
      case SetLit(es@_*) => SetLit(es.map(_.subst(x, e)) :_*)
      case Union(e1, e2) => Union(e1.subst(x, e), e2.subst(x, e))
      case Diff(e1, e2) => Diff(e1.subst(x, e), e2.subst(x, e))
      case ISect(e1, e2) => ISect(e1.subst(x, e), e2.subst(x, e))
      case SetVar(name) => SetVar(name)
      case SetSymbol(c, id) => SetSymbol(c, id)
    }
  }

  implicit class SubstBoolExpr(p: BoolExpr) extends Subst[BoolExpr] {
    override def toT = p

    override def subst(x: Symbols, e: SetExpr): BoolExpr = p match {
      case Eq(e1, e2) => Eq(e1.subst(x, e), e2.subst(x, e))
      case ClassMem(e1, s) => ClassMem(e1.subst(x, e), s)
      case SetMem(e1, e2) =>
        val ee2 = e2.subst(x, e)
        SetMem(e1, ee2)
      case SetSubEq(e1, e2) => SetSubEq(e1.subst(x, e), e2.subst(x, e))
      case True => True
      case And(p1, p2) => And(p1.subst(x, e), p2.subst(x, e))
      case Not(pp) => Not(pp.subst(x,e))
    }

    override def subst(x: Symbols, e: BasicExpr): BoolExpr = p match {
      case Eq(e1, e2) => Eq(e1.subst(x, e), e2.subst(x, e))
      case ClassMem(e1, s) => ClassMem(e1.subst(x, e), s)
      case SetMem(e1, e2) =>
        val ee2 = e2.subst(x, e)
        SetMem(e1, ee2)
      case SetSubEq(e1, e2) => SetSubEq(e1.subst(x, e), e2.subst(x, e))
      case True => True
      case And(p1, p2) => And(p1.subst(x, e), p2.subst(x, e))
      case Not(pp) => Not(pp.subst(x,e))
    }
  }

  implicit class SubstProp(pi: Prop) extends Subst[Prop] {
    override def toT = pi

    override def subst(x: Symbols, e: SetExpr): Prop   = pi.map(_.subst(x, e))
    override def subst(x: Symbols, e: BasicExpr): Prop = pi.map(_.subst(x, e))
  }


  implicit class SubstSpatialDesc(sd: SpatialDesc) extends Subst[SpatialDesc] {
    override def toT = sd

    override def subst(x: Symbols, e: BasicExpr): SpatialDesc = sd match {
      case AbstractDesc(c) => AbstractDesc(c)
      case ConcreteDesc(c, children, refs) => ConcreteDesc(c, children.mapValues(_.subst(x, e)), refs.mapValues(_.subst(x, e)))
    }

    override def subst(x: Symbols, e: SetExpr): SpatialDesc = sd match {
      case AbstractDesc(c) => AbstractDesc(c)
      case ConcreteDesc(c, children, refs) => ConcreteDesc(c, children.mapValues(_.subst(x, e)), refs.mapValues(_.subst(x, e)))
    }
  }

  implicit class SubstSpatial[T](spatial: Spatial[T]) extends Subst[Spatial[T]] {
    override def toT = spatial

    override def subst(x: Symbols, e: BasicExpr): Spatial[T] =
    e match {
      case Symbol(id) =>
        spatial.mapValues(_.subst(x, e))
      case Var(name) =>
        spatial.mapValues(_.subst(x, e))
    }

    override def subst(x: Symbols, e: SetExpr): Spatial[T] = spatial.mapValues(_.subst(x, e))
  }

  implicit class SubstQSpatial(qspatial: Set[QSpatial]) extends Subst[Set[QSpatial]] {
    override def toT = qspatial

    // Be careful about name capture and think about expansion
    override def subst(x: Symbols, e: BasicExpr): Set[QSpatial] =
      qspatial.map(_qs_e.modify(_.subst(x, e)))

    override def subst(x: Symbols, e: SetExpr): Set[QSpatial] =
      qspatial.map(_qs_e.modify(_.subst(x, e)))
  }


  implicit class SubstSHeap(heap : SHeap) extends Subst[SHeap] {
    override def toT = heap

    override def subst(x: Symbols, e: BasicExpr): SHeap =
      SHeap(heap.spatial.subst(x, e), heap.qspatial.subst(x, e), heap.pure.subst(x, e))
    override def subst(x: Symbols, e: SetExpr): SHeap =
      SHeap(heap.spatial.subst(x, e), heap.qspatial.subst(x, e), heap.pure.subst(x, e))
  }

  implicit class SubstSStack(stack : SStack) extends Subst[SStack] {
    override def toT = stack

    override def subst(x: Symbols, e: BasicExpr): SStack = stack.mapValues(_.subst(x, e))

    override def subst(x: Symbols, e: SetExpr): SStack = stack.mapValues(_.subst(x, e))
  }

  implicit class SubstSMem(mem : SMem) extends Subst[SMem] {
    override def toT = mem

    override def subst(x: Symbols, e: BasicExpr): SMem =
      SMem(mem.stack.subst(x, e), mem.heap.subst(x, e))

    override def subst(x: Symbols, e: SetExpr): SMem =
      SMem(mem.stack.subst(x, e), mem.heap.subst(x, e))
  }
}
