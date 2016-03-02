package semantics
package domains

import scala.language.higherKinds

import monocle.macros.{GenLens, GenPrism}
import syntax.ast._

case class Loc(id: Int)

sealed trait DescType
case object ExactDesc extends DescType
case object AbstractDesc extends DescType
case class PartialDesc(hasExact: Boolean, possible: Set[Class]) extends DescType

sealed trait Ownership
case object NewlyCreated extends Ownership
case object Unowned extends Ownership
case object UnknownOwner extends Ownership
case class  Owned(l : Loc, f : Fields) extends Ownership

sealed trait SOwnership
case object SUnowned        extends SOwnership
case object SRef            extends SOwnership
case class  SOwned(l : Loc, f : Fields) extends SOwnership

object DescType {
  val _dt_partial = GenPrism[DescType, PartialDesc]
}

case class SpatialDesc(cl : Class, desctype : DescType, children : Map[Fields, SetExpr[IsSymbolic.type]], refs : Map[Fields, SetExpr[IsSymbolic.type]], descendantpools: DescendantPools)

object SpatialDesc {
  val _sd_c = GenLens[SpatialDesc](_.cl)
  val _sd_desctype = GenLens[SpatialDesc](_.desctype)
  val _sd_children = GenLens[SpatialDesc](_.children)
  val _sd_refs = GenLens[SpatialDesc](_.refs)
  val _sd_descendantpools = GenLens[SpatialDesc](_.descendantpools)
}

case class SSymbolDesc(cl : Class, crd : Cardinality, ownership : SOwnership, descendantPools: DescendantPools)

sealed trait SymbolDesc
case class Loced(l : Loc) extends SymbolDesc
case class UnknownLoc(cl : Class, ownership : SOwnership, descendantPools: DescendantPools) extends SymbolDesc

case class SHeap(ssvltion : SetSymbolValuation, svltion : SymbolValuation, locOwnership: LocOwnership, initSpatial: Spatial, currentSpatial: Spatial, pure : Prop)

object SHeap {
  val _sh_ssvltion       = GenLens[SHeap](_.ssvltion)
  val _sh_svltion        = GenLens[SHeap](_.svltion)
  val _sh_locOwnership   = GenLens[SHeap](_.locOwnership)
  val _sh_initSpatial    = GenLens[SHeap](_.initSpatial)
  val _sh_currentSpatial = GenLens[SHeap](_.currentSpatial)
  val _sh_pure           = GenLens[SHeap](_.pure)

  def initial(ssvltion : SetSymbolValuation, svltion : SymbolValuation, locOwnership: LocOwnership, spatial : Spatial, pure: Prop) =
    SHeap(ssvltion, svltion, locOwnership, spatial, spatial, pure)
}

case class SMem(stack: SStack, heap: SHeap)

object SMem {
  val _sm_stack = GenLens[SMem](_.stack)
  val _sm_heap = GenLens[SMem](_.heap)
}


case class CHeap(typeenv: Map[Instances, Class],
                 childenv: Map[Instances, Map[Fields, Set[Instances]]],
                 refenv: Map[Instances, Map[Fields, Set[Instances]]])

object CHeap {
  val _ch_typeenv  = GenLens[CHeap](_.typeenv)
  val _ch_childenv = GenLens[CHeap](_.childenv)
  val _ch_refenv   = GenLens[CHeap](_.refenv)
}

case class CMem(stack: CStack, heap: CHeap)

object CMem {
  val _cm_stack = GenLens[CMem](_.stack)
  val _cm_heap  = GenLens[CMem](_.heap)
}