package semantics

import syntax.ast._
import semantics.domains._
import semantics.domains.QSpatial._

trait Subst[T] {
  def toT : T

  def subst(x : Symbols, e : BasicExpr[IsSymbolic.type]) : T
  def subst(x : Symbols, e : SetExpr[IsSymbolic.type])   : T
  def subst_all[B <: BasicExpr[IsSymbolic.type]](th : Map[Symbols, B])(implicit fromT: T => Subst[T]) : T =
    th.foldLeft(toT)((t : T, kv : (Symbols, B)) => t.subst(kv._1, kv._2))
  def subst_all[S <: SetExpr[IsSymbolic.type]](th : Map[Symbols, S])(implicit fromT: T => Subst[T], dummy: DummyImplicit) : T =
    th.foldLeft(toT)((t : T, kv : (Symbols, S)) => t.subst(kv._1, kv._2))
}

object Subst {

  implicit class SubstBasicExpr(e0: BasicExpr[IsSymbolic.type]) extends Subst[BasicExpr[IsSymbolic.type]] {
    override def toT = e0

    override def subst(x: Symbols, e1: SetExpr[IsSymbolic.type]): BasicExpr[IsSymbolic.type] = e0
    override def subst(x: Symbols, e1: BasicExpr[IsSymbolic.type]): BasicExpr[IsSymbolic.type] = e0 match {
      case Symbol(id) if id == x => e1
    }
  }

  implicit class SubstExpr(e0: SetExpr[IsSymbolic.type]) extends Subst[SetExpr[IsSymbolic.type]] {
    override def toT = e0

    override def subst(x: Symbols, e: SetExpr[IsSymbolic.type]): SetExpr[IsSymbolic.type] = e0 match {
      case SetLit(es@_*) => SetLit(es :_*)
      case Union(e1, e2) => Union(e1.subst(x, e), e2.subst(x, e))
      case Diff(e1, e2) => Diff(e1.subst(x, e), e2.subst(x, e))
      case ISect(e1, e2) => ISect(e1.subst(x, e), e2.subst(x, e))
      case SetSymbol(id) if id == x => e
      case SetSymbol(id) => SetSymbol(id)
    }

    override def subst(x: Symbols, e: BasicExpr[IsSymbolic.type]): SetExpr[IsSymbolic.type] = e0 match {
      case SetLit(es@_*) => SetLit(es.map(_.subst(x, e)) :_*)
      case Union(e1, e2) => Union(e1.subst(x, e), e2.subst(x, e))
      case Diff(e1, e2) => Diff(e1.subst(x, e), e2.subst(x, e))
      case ISect(e1, e2) => ISect(e1.subst(x, e), e2.subst(x, e))
      case SetSymbol(id) => SetSymbol(id)
    }
  }

  implicit class SubstBoolExpr(p: BoolExpr[IsSymbolic.type]) extends Subst[BoolExpr[IsSymbolic.type]] {
    override def toT = p

    override def subst(x: Symbols, e: SetExpr[IsSymbolic.type]): BoolExpr[IsSymbolic.type] = p match {
      case Eq(e1, e2) => Eq(e1.subst(x, e), e2.subst(x, e))
      case SetMem(e1, e2) =>
        val ee2 = e2.subst(x, e)
        SetMem(e1, ee2)
      case SetSubEq(e1, e2) => SetSubEq(e1.subst(x, e), e2.subst(x, e))
      case True() => True()
      case And(p1, p2) => And(p1.subst(x, e), p2.subst(x, e))
      case Not(pp) => Not(pp.subst(x,e))
    }

    override def subst(x: Symbols, e: BasicExpr[IsSymbolic.type]): BoolExpr[IsSymbolic.type] = p match {
      case Eq(e1, e2) => Eq(e1.subst(x, e), e2.subst(x, e))
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

    override def subst(x: Symbols, e: SetExpr[IsSymbolic.type]): Prop   = pi.map(_.subst(x, e))
    override def subst(x: Symbols, e: BasicExpr[IsSymbolic.type]): Prop = pi.map(_.subst(x, e))
  }


  implicit class SubstSpatialDesc(sd: SpatialDesc) extends Subst[SpatialDesc] {
    override def toT = sd

    override def subst(x: Symbols, e: BasicExpr[IsSymbolic.type]): SpatialDesc = sd match {
      case SpatialDesc(c, typ, children, refs) => SpatialDesc(c, typ, children.mapValues(_.subst(x, e)), refs.mapValues(_.subst(x, e)))
    }

    override def subst(x: Symbols, e: SetExpr[IsSymbolic.type]): SpatialDesc = sd match {
      case SpatialDesc(c, typ, children, refs) => SpatialDesc(c, typ, children.mapValues(_.subst(x, e)), refs.mapValues(_.subst(x, e)))
    }
  }

  implicit class SubstSpatial[T](spatial: Spatial[T]) extends Subst[Spatial[T]] {
    override def toT = spatial

    override def subst(x: Symbols, e: BasicExpr[IsSymbolic.type]): Spatial[T] = e match {
      case Symbol(id) =>
        spatial.mapValues(_.subst(x, e))
    }

    override def subst(x: Symbols, e: SetExpr[IsSymbolic.type]): Spatial[T] = spatial.mapValues(_.subst(x, e))
  }

  implicit class SubstQSpatial(qspatial: Set[QSpatial]) extends Subst[Set[QSpatial]] {
    override def toT = qspatial

    // Be careful about name capture and think about expansion
    override def subst(x: Symbols, e: BasicExpr[IsSymbolic.type]): Set[QSpatial] =
      qspatial.map(_qs_e.modify(_.subst(x, e)))

    override def subst(x: Symbols, e: SetExpr[IsSymbolic.type]): Set[QSpatial] =
      qspatial.map(_qs_e.modify(_.subst(x, e)))
  }


  implicit class SubstSHeap(heap : SHeap) extends Subst[SHeap] {
    override def toT = heap

    override def subst(x: Symbols, e: BasicExpr[IsSymbolic.type]): SHeap =
      SHeap(heap.spatial.subst(x, e), heap.qspatial.subst(x, e), heap.pure.subst(x, e))
    override def subst(x: Symbols, e: SetExpr[IsSymbolic.type]): SHeap =
      SHeap(heap.spatial.subst(x, e), heap.qspatial.subst(x, e), heap.pure.subst(x, e))
  }

  implicit class SubstSStack(stack : SStack) extends Subst[SStack] {
    override def toT = stack

    override def subst(x: Symbols, e: BasicExpr[IsSymbolic.type]): SStack = stack.mapValues(_.subst(x, e))

    override def subst(x: Symbols, e: SetExpr[IsSymbolic.type]): SStack = stack.mapValues(_.subst(x, e))
  }

  implicit class SubstSMem(mem : SMem) extends Subst[SMem] {
    override def toT = mem

    override def subst(x: Symbols, e: BasicExpr[IsSymbolic.type]): SMem =
      SMem(mem.stack.subst(x, e), mem.heap.subst(x, e))

    override def subst(x: Symbols, e: SetExpr[IsSymbolic.type]): SMem =
      SMem(mem.stack.subst(x, e), mem.heap.subst(x, e))
  }
}
