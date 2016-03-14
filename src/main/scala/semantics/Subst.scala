package semantics

import syntax.ast._
import semantics.domains._

trait Subst[T] {
  def toT : T

  def subst(x : Symbol, y : Symbol) : T
  def subst(x : SetSymbol, e : SetExpr[IsSymbolic.type]) : T
  def subst_all(th : Map[Symbol, Symbol])(implicit fromT: T => Subst[T]) : T =
    th.foldLeft(toT) { (t, kv) => kv match { case (k, v) => t.subst(k, v) } }
  def subst_all[S <: SetExpr[IsSymbolic.type]](th : Map[SetSymbol, S])(implicit fromT: T => Subst[T], dummy: DummyImplicit) : T =
    th.foldLeft(toT) { (t, kv) => kv match { case (k, v) => t.subst(k, v) } }
}

object Subst {

  implicit class SubstBasicExpr(e0: BasicExpr[IsSymbolic.type]) extends Subst[BasicExpr[IsSymbolic.type]] {
    override def toT = e0

    override def subst(x: Symbol, y: Symbol): BasicExpr[IsSymbolic.type] = e0 match {
      case `x` => y
      case _ => e0
    }

    override def subst(x: SetSymbol, e: SetExpr[IsSymbolic.type]): BasicExpr[IsSymbolic.type] = e0
  }

  implicit class SubstExpr(e0: SetExpr[IsSymbolic.type]) extends Subst[SetExpr[IsSymbolic.type]] {
    override def toT = e0

    override def subst(x: Symbol, y: Symbol): SetExpr[IsSymbolic.type] = e0 match {
      case SetLit(es) => SetLit(es.map(_.subst(x,y)))
      case Union(e1, e2) => Union(e1.subst(x, y), e2.subst(x, y))
      case Diff(e1, e2) => Diff(e1.subst(x, y), e2.subst(x, y))
      case ISect(e1, e2) => ISect(e1.subst(x, y), e2.subst(x, y))
      case SetSymbol(id) => e0
    }

    override def subst(x: SetSymbol, e: SetExpr[IsSymbolic.type]): SetExpr[IsSymbolic.type] = e0 match {
      case `x` => e
      case SetLit(es) => SetLit(es)
      case Union(e1, e2) => Union(e1.subst(x, e), e2.subst(x, e))
      case Diff(e1, e2) => Diff(e1.subst(x, e), e2.subst(x, e))
      case ISect(e1, e2) => ISect(e1.subst(x, e), e2.subst(x, e))
      case SetSymbol(id) => SetSymbol(id)
    }
  }

  implicit class SubstBoolExpr(p: BoolExpr[IsSymbolic.type]) extends Subst[BoolExpr[IsSymbolic.type]] {
    override def toT = p

    override def subst(x: Symbol, y: Symbol): BoolExpr[IsSymbolic.type] = p match {
      case Eq(e1, e2) => Eq(e1.subst(x, y), e2.subst(x, y))
      case SetMem(e1, e2) => SetMem(e1.subst(x, y), e2.subst(x, y))
      case SetSubEq(e1, e2) => SetSubEq(e1.subst(x, y), e2.subst(x, y))
      case And(b1, b2) => And(b1.subst(x, y), b2.subst(x, y))
      case True() => True()
      case Not(b) => Not(b.subst(x, y))
    }

    override def subst(x: SetSymbol, e: SetExpr[IsSymbolic.type]): BoolExpr[IsSymbolic.type] = p match {
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

    override def subst(x: Symbol, y: Symbol): Prop = pi.map(_.subst(x, y))

    override def subst(x: SetSymbol, e: SetExpr[IsSymbolic.type]): Prop   = pi.map(_.subst(x, e))
  }


  implicit class SubstSpatialDesc(sd: SpatialDesc) extends Subst[SpatialDesc] {
    override def toT = sd

    override def subst(x: Symbol, y: Symbol): SpatialDesc = sd match {
      case SpatialDesc(c, typ, children, refs, descendantpool) => SpatialDesc(c, typ, children.mapValues(_.subst(x, y)), refs.mapValues(_.subst(x, y)), descendantpool.mapValues(_.subst(x, y)))
    }

    override def subst(x: SetSymbol, e: SetExpr[IsSymbolic.type]): SpatialDesc = sd match {
      case SpatialDesc(c, typ, children, refs, descendantpool) => SpatialDesc(c, typ, children.mapValues(_.subst(x, e)), refs.mapValues(_.subst(x, e)), descendantpool.mapValues(_.subst(x, e)))
    }
  }

  implicit class SubstSpatial(spatial: Spatial) extends Subst[Spatial] {
    override def toT = spatial

    override def subst(x: Symbol, y: Symbol): Spatial = spatial.mapValues(_.subst(x, y))

    override def subst(x: SetSymbol, e: SetExpr[IsSymbolic.type]): Spatial = spatial.mapValues(_.subst(x, e))
  }

  implicit class SubstSetSymbolValuation(ssvaluation: SetSymbolValuation) extends Subst[SetSymbolValuation] {
    override def toT = ssvaluation

    override def subst(x: Symbol, y: Symbol): SetSymbolValuation = ssvaluation

    override def subst(x: SetSymbol, e: SetExpr[IsSymbolic.type]): SetSymbolValuation = ssvaluation - x
  }

  implicit class SubstSymbolValuation(svaluation: SymbolValuation) extends Subst[SymbolValuation] {
    override def toT = svaluation

    override def subst(x: Symbol, y: Symbol): SymbolValuation = svaluation - x

    override def subst(x: SetSymbol, e: SetExpr[IsSymbolic.type]): SymbolValuation = svaluation
  }

  implicit class SubstSHeap(heap : SHeap) extends Subst[SHeap] {
    override def toT = heap

    override def subst(x: Symbol, y: Symbol): SHeap =
      SHeap(heap.ssvltion.subst(x, y),
            heap.svltion.subst(x, y),
            heap.locOwnership,
            heap.initSpatial.subst(x, y),
            heap.currentSpatial.subst(x, y),
            heap.pure.subst(x, y))

    override def subst(x: SetSymbol, e: SetExpr[IsSymbolic.type]): SHeap =
      SHeap(heap.ssvltion.subst(x, e),
        heap.svltion.subst(x, e),
        heap.locOwnership,
        heap.initSpatial.subst(x, e),
        heap.currentSpatial.subst(x, e),
        heap.pure.subst(x, e))
  }

  implicit class SubstSStack(stack : SStack) extends Subst[SStack] {
    override def toT = stack

    override def subst(x: Symbol, y: Symbol): SStack = stack.mapValues(_.subst(x, y))

    override def subst(x: SetSymbol, e: SetExpr[IsSymbolic.type]): SStack = stack.mapValues(_.subst(x, e))
  }

  implicit class SubstSMem(mem : SMem) extends Subst[SMem] {
    override def toT = mem

    override def subst(x: Symbol, y: Symbol): SMem =
      SMem(mem.initStack.subst(x,y), mem.currentStack.subst(x,y), mem.heap.subst(x, y))

    override def subst(x: SetSymbol, e: SetExpr[IsSymbolic.type]): SMem =
      SMem(mem.initStack.subst(x, e), mem.currentStack.subst(x, e), mem.heap.subst(x, e))
  }
}
