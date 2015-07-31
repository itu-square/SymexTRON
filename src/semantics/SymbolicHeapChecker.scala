package semantics

import helper._
import semantics.Subst._
import syntax.ast._

object SymbolicHeapChecker {

  // NOTICE: May need to rerun when having lists/trees or advanced checkers due to guard checks that may become valid
  // Alternatively have a separate phase for non-pointing spatial constraints (list/trees/checkers)
  private def resolveSpatialConstraints(h1: Spatial) : Prop = {
    for (e1 <- h1.keySet)
      yield {
        (for (e2 <- h1.keySet; if e1 != e2)
          yield {
            Not(Eq(e1, e2))
          }) + Not(Eq(e1, Nil()))
      }
  }.flatten

  private def propagatePureConstraints(h1: SymbolicHeap, h2: SymbolicHeap): Option[(SymbolicHeap, SymbolicHeap)] = {
    def ppc(pi1 : Prop, sig1 : Spatial, pi2 : Prop, sig2 : Spatial, pih : Prop)
            : Option[(SymbolicHeap, SymbolicHeap)] = {
      if (pi1.size <= 0) Some (SymbolicHeap(pih, sig1), SymbolicHeap(pi2, sig2))
      else pi1.head match {
        case Eq(e1, e2) if e1 == e2 => ppc(pi1.tail, sig1, pi2, sig2, pih)
        case Eq(Var(x), e2) =>
          ppc(pi1.tail.subst(x, e2), sig1.subst(x, e2), pi2.subst(x, e2), sig2.subst(x, e2), pih.subst(x, e2))
        case Eq(e1, Var(x)) =>
          ppc(pi1.tail.subst(x, e1), sig1.subst(x, e1), pi2.subst(x, e1), sig2.subst(x, e1), pih.subst(x, e1))
        case Not(Eq(e1, e2)) if e1 == e2 => None
        case p => ppc(pi1.tail, sig1, pi2, sig2, pih + p)
      }
    }
    ppc(h1.pi, h1.sig, h2.pi, h2.sig, Set())
  }

  def satSplit(h1: SymbolicHeap, h2: SymbolicHeap) : Set[(SymbolicHeap, SymbolicHeap)] = {
     var hsold = Set[(SymbolicHeap, SymbolicHeap)]()
     var hs    = Set((h1, h2))
     while(hsold != hs) {
       hsold = hs
       if (hs.size > 0) {
         val hh = hs.head
         hs = hs.tail
         propagatePureConstraints(hh._1, hh._2) match {
           case Some(hh2) => ???
           case None => ???
         }
       }
     }
  }

  private def normalise(h1: SymbolicHeap, h2: SymbolicHeap) : Set[(SymbolicHeap, SymbolicHeap)] = {
    val newprop = resolveSpatialConstraints(h1.sig)
    val newh1 = SymbolicHeap(h1.pi ++ newprop, h1.sig)
    satSplit(newh1, h2)
    // TODO: Add SAT search phase, hint: consider only operator relevant variables in search
  }

  private def subtract(h1: SymbolicHeap, h2: SymbolicHeap): Boolean = ???

  def oracle(h1: SymbolicHeap, h2: SymbolicHeap): Boolean = {
    val newhs = normalise(h1, h2)
    newhs.forall(hs => subtract(hs._1, hs._2))
  }
  def incon(h : SymbolicHeap) : Boolean = SymbolicHeapChecker.oracle(h, SymbolicHeap(Set(Eq(Nil(), Nil())), Map()))

  def allocd(h : SymbolicHeap, e : Expr) : Boolean = {
    incon(SymbolicHeap(h.pi, h.sig.adjust(e) {_ + Map()})) &&
      incon(SymbolicHeap(h.pi + Eq(e, Nil()), h.sig))
  }

}
