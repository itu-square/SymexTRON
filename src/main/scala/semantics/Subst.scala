package semantics

import syntax.ast.QSpatial._
import syntax.ast._

trait Subst[T] {
  def toT : T

  def subst(x : Symbols, e : BasicExpr[IsSymbolic]) : T
  def subst(x : Symbols, e : SetExpr[IsSymbolic])   : T
  def subst_all[B <: BasicExpr[IsSymbolic]](th : Map[Symbols, B])(implicit fromT: T => Subst[T]) : T =
    th.foldLeft(toT)((t : T, kv : (Symbols, B)) => t.subst(kv._1, kv._2))
  def subst_all[S <: SetExpr[IsSymbolic]](th : Map[Symbols, S])(implicit fromT: T => Subst[T], dummy: DummyImplicit) : T =
    th.foldLeft(toT)((t : T, kv : (Symbols, S)) => t.subst(kv._1, kv._2))
}

object Subst {

  implicit class SubstBasicExpr(e0: BasicExpr[IsSymbolic]) extends Subst[BasicExpr[IsSymbolic]] {
    override def toT = e0

    override def subst(x: Symbols, e1: SetExpr[IsSymbolic]): BasicExpr[IsSymbolic] = e0
    override def subst(x: Symbols, e1: BasicExpr[IsSymbolic]): BasicExpr[IsSymbolic] = e0 match {
      case Symbol(id) if id == x => e1
    }
  }

  implicit class SubstExpr(e0: SetExpr[IsSymbolic]) extends Subst[SetExpr[IsSymbolic]] {
    override def toT = e0

    override def subst(x: Symbols, e: SetExpr[IsSymbolic]): SetExpr[IsSymbolic] = e0 match {
      case SetLit(es@_*) => SetLit(es :_*)
      case Union(e1, e2) => Union(e1.subst(x, e), e2.subst(x, e))
      case Diff(e1, e2) => Diff(e1.subst(x, e), e2.subst(x, e))
      case ISect(e1, e2) => ISect(e1.subst(x, e), e2.subst(x, e))
      case SetSymbol(_,id) if id == x => e
      case SetSymbol(c, id) => SetSymbol(c, id)
    }

    override def subst(x: Symbols, e: BasicExpr[IsSymbolic]): SetExpr[IsSymbolic] = e0 match {
      case SetLit(es@_*) => SetLit(es.map(_.subst(x, e)) :_*)
      case Union(e1, e2) => Union(e1.subst(x, e), e2.subst(x, e))
      case Diff(e1, e2) => Diff(e1.subst(x, e), e2.subst(x, e))
      case ISect(e1, e2) => ISect(e1.subst(x, e), e2.subst(x, e))
      case SetSymbol(c, id) => SetSymbol(c, id)
    }
  }

  implicit class SubstBoolExpr(p: BoolExpr[IsSymbolic]) extends Subst[BoolExpr[IsSymbolic]] {
    override def toT = p

    override def subst(x: Symbols, e: SetExpr[IsSymbolic]): BoolExpr[IsSymbolic] = p match {
      case Eq(e1, e2) => Eq(e1.subst(x, e), e2.subst(x, e))
      case ClassMem(e1, s) => ClassMem(e1.subst(x, e), s)
      case SetMem(e1, e2) =>
        val ee2 = e2.subst(x, e)
        SetMem(e1, ee2)
      case SetSubEq(e1, e2) => SetSubEq(e1.subst(x, e), e2.subst(x, e))
      case True() => True()
      case And(p1, p2) => And(p1.subst(x, e), p2.subst(x, e))
      case Not(pp) => Not(pp.subst(x,e))
    }

    override def subst(x: Symbols, e: BasicExpr[IsSymbolic]): BoolExpr[IsSymbolic] = p match {
      case Eq(e1, e2) => Eq(e1.subst(x, e), e2.subst(x, e))
      case ClassMem(e1, s) => ClassMem(e1.subst(x, e), s)
      case SetMem(e1, e2) =>
        val ee2 = e2.subst(x, e)
        SetMem(e1, ee2)
      case SetSubEq(e1, e2) => SetSubEq(e1.subst(x, e), e2.subst(x, e))
      case True() => True()
      case And(p1, p2) => And(p1.subst(x, e), p2.subst(x, e))
      case Not(pp) => Not(pp.subst(x,e))
    }
  }

  implicit class SubstProp(pi: Prop) extends Subst[Prop] {
    override def toT = pi

    override def subst(x: Symbols, e: SetExpr[IsSymbolic]): Prop   = pi.map(_.subst(x, e))
    override def subst(x: Symbols, e: BasicExpr[IsSymbolic]): Prop = pi.map(_.subst(x, e))
  }


  implicit class SubstSpatialDesc(sd: SpatialDesc) extends Subst[SpatialDesc] {
    override def toT = sd

    override def subst(x: Symbols, e: BasicExpr[IsSymbolic]): SpatialDesc = sd match {
      case AbstractDesc(c) => AbstractDesc(c)
      case ConcreteDesc(c, children, refs) => ConcreteDesc(c, children.mapValues(_.subst(x, e)), refs.mapValues(_.subst(x, e)))
    }

    override def subst(x: Symbols, e: SetExpr[IsSymbolic]): SpatialDesc = sd match {
      case AbstractDesc(c) => AbstractDesc(c)
      case ConcreteDesc(c, children, refs) => ConcreteDesc(c, children.mapValues(_.subst(x, e)), refs.mapValues(_.subst(x, e)))
    }
  }

  implicit class SubstSpatial[T](spatial: Spatial[T]) extends Subst[Spatial[T]] {
    override def toT = spatial

    override def subst(x: Symbols, e: BasicExpr[IsSymbolic]): Spatial[T] = e match {
      case Symbol(id) =>
        spatial.mapValues(_.subst(x, e))
    }

    override def subst(x: Symbols, e: SetExpr[IsSymbolic]): Spatial[T] = spatial.mapValues(_.subst(x, e))
  }

  implicit class SubstQSpatial(qspatial: Set[QSpatial]) extends Subst[Set[QSpatial]] {
    override def toT = qspatial

    // Be careful about name capture and think about expansion
    override def subst(x: Symbols, e: BasicExpr[IsSymbolic]): Set[QSpatial] =
      qspatial.map(_qs_e.modify(_.subst(x, e)))

    override def subst(x: Symbols, e: SetExpr[IsSymbolic]): Set[QSpatial] =
      qspatial.map(_qs_e.modify(_.subst(x, e)))
  }


  implicit class SubstSHeap(heap : SHeap) extends Subst[SHeap] {
    override def toT = heap

    override def subst(x: Symbols, e: BasicExpr[IsSymbolic]): SHeap =
      SHeap(heap.spatial.subst(x, e), heap.qspatial.subst(x, e), heap.pure.subst(x, e))
    override def subst(x: Symbols, e: SetExpr[IsSymbolic]): SHeap =
      SHeap(heap.spatial.subst(x, e), heap.qspatial.subst(x, e), heap.pure.subst(x, e))
  }

  implicit class SubstSStack(stack : SStack) extends Subst[SStack] {
    override def toT = stack

    override def subst(x: Symbols, e: BasicExpr[IsSymbolic]): SStack = stack.mapValues(_.subst(x, e))

    override def subst(x: Symbols, e: SetExpr[IsSymbolic]): SStack = stack.mapValues(_.subst(x, e))
  }

  implicit class SubstSMem(mem : SMem) extends Subst[SMem] {
    override def toT = mem

    override def subst(x: Symbols, e: BasicExpr[IsSymbolic]): SMem =
      SMem(mem.stack.subst(x, e), mem.heap.subst(x, e))

    override def subst(x: Symbols, e: SetExpr[IsSymbolic]): SMem =
      SMem(mem.stack.subst(x, e), mem.heap.subst(x, e))
  }
}
