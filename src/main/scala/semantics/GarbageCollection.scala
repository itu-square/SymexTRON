package semantics

import syntax.ast._
import semantics.domains._

/**
  * Created by asal on 16/01/2016.
  */
object GarbageCollection {

  def retainVars(cmem: CMem, retained: Set[Vars]): CMem = {
    def mark(marked: Set[Instances], current: Instances): Set[Instances] = {
      def markRefs(marked: Set[Instances], refs: Map[Instances, Map[Fields, Set[Instances]]]): Set[Instances] = {
        if (refs.contains(current)) {
          val orefs = refs(current).values.toSet.flatten
          orefs.foldLeft(marked) { (marked, o) =>
            if (!marked.contains(o)) mark(marked + o, o) else marked
          }
        } else marked
      }
      val childsmarked = markRefs(marked, cmem.heap.childenv)
      val refsmarked = markRefs(childsmarked, cmem.heap.refenv)
      refsmarked
    }
    def sweep[V](marked: Set[Instances], m: Map[Instances, V]): Map[Instances, V] = {
      m.filterKeys(marked.contains)
    }
    val newstack = cmem.stack.filterKeys(v => retained.contains(v))
    val marked = newstack.values.toSet.flatten
    val marked_ = marked.foldLeft(marked)(mark)
    val newheap = CHeap(sweep(marked_, cmem.heap.typeenv),
                        sweep(marked_, cmem.heap.childenv),
                        sweep(marked_, cmem.heap.childenv))
    CMem(newstack, newheap)
  }

  def gc(cmem: CMem): CMem = retainVars(cmem, cmem.stack.keys.toSet)

}
