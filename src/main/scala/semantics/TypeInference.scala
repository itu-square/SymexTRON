package semantics

import syntax.ast._
import semantics.domains._


class TypeInference(defs: Map[Class, ClassDefinition]) {

  def lub(c1 : Class, c2 : Class) : Class = {
    val commonSupers = (defs.supertypes(c1) + c1) intersect
                          (defs.supertypes(c2) + c2)
    val res = commonSupers.foldLeft(Class("Any"))((ub, c) =>
      if(defs.supertypes(c) contains ub) c else ub)
    res
  }

  def glb(c1 : Class, c2 : Class) : Class = {
    val sts = defs.subtypes
    val commonSubs = sts(c1) intersect sts(c2)
    commonSubs.foldLeft(Class("Nothing"))((lb, c) =>
      if (sts(c) contains lb) c else lb)
  }

  // TODO Do this more safely
  def inferType(e : BasicExpr[IsSymbolic.type], h : SHeap) : Class = e match {
    case Symbol(id) => SpatialDesc._sd_c.get(h.spatial(id))
  }

  def inferType(e : SetExpr[IsSymbolic.type], h : SHeap) : Class = e match {
    case SetLit(es@_*) => es.foldLeft(Class("Nothing"))((c, e) =>
      lub(c, inferType(e, h)))
    case Union(e1, e2) => lub(inferType(e1, h), inferType(e2, h))
    case Diff(e1, e2) => inferType(e1, h)
    case ISect(e1, e2) => glb(inferType(e1, h), inferType(e2, h))
    case SetSymbol((cl, crd), id) => cl
  }
}
