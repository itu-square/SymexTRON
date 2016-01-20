package semantics
package domains

import scala.language.higherKinds

import monocle.macros.{GenLens, GenPrism}
import syntax.ast._

sealed trait DescType
case object ExactDesc extends DescType
case object AbstractDesc extends DescType
case class PartialDesc(hasExact: Boolean, possible: Set[Class]) extends DescType

object DescType {
  val _dt_partial = GenPrism[DescType, PartialDesc]
}

case class SpatialDesc(c : Class, typ : DescType, children : Map[Fields, SetExpr[IsSymbolic.type]], refs : Map[Fields, SetExpr[IsSymbolic.type]])

object SpatialDesc {
  val _sd_c = GenLens[SpatialDesc](_.c)
  val _sd_typ = GenLens[SpatialDesc](_.typ)
  val _sd_children = GenLens[SpatialDesc](_.children)
  val _sd_refs = GenLens[SpatialDesc](_.refs)
}

case class QSpatial(e : SetExpr[IsSymbolic.type], c : Class)

object QSpatial {
  val _qs_e = GenLens[QSpatial](_.e)
  val _qs_c = GenLens[QSpatial](_.c)
}

case class QJump(source : SetExpr[IsSymbolic.type], c : Class, target : SetExpr[IsSymbolic.type])

object QJump {
  val _qj_source = GenLens[QJump](_.source)
  val _qj_c = GenLens[QJump](_.c)
  val _qj_target = GenLens[QJump](_.target)
}

case class SHeap(spatial: Spatial, qspatial: Set[QSpatial], pure : Prop)

object SHeap {
  val _sh_spatial  = GenLens[SHeap](_.spatial)
  val _sh_qspatial = GenLens[SHeap](_.qspatial)
  val _sh_pure     = GenLens[SHeap](_.pure)
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