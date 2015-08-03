package semantics

import helper._
import semantics.Subst._
import syntax.ast._

import FreeVariables._

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

  private def propagateConstraints(h1: SymbolicHeap, h2: SymbolicHeap): Option[(SymbolicHeap, SymbolicHeap)] = {
    for (hh <- propagatePureConstraints(h1, h2);
         if hh._1.sig.find(p => p._2.size != 1).isEmpty) //Ensure that all spatial elements are defined at most once
      yield hh
  }

  def satSplit(h1: SymbolicHeap, h2: SymbolicHeap) : Set[(SymbolicHeap, SymbolicHeap)] = {
     var hsold = Set[(SymbolicHeap, SymbolicHeap)]()
     var hs    = Set((h1, h2))
     while(hsold != hs) {
       hsold = hs
       if (hs.size > 0) {
         var hsvisited = Set[(SymbolicHeap, SymbolicHeap)]()
         for (hh <- hs) {
           propagateConstraints(hh._1, hh._2) match {
             case Some(hh2) => {
               val es = (hh2._1.freevars ++ hh2._2.freevars).map[Expr, Set[Expr]](Var(_)) + Nil()
               val eps = for (e1 <- es; e2 <- es; if e1 != e2) yield (e1, e2)
               (for (ep <- eps.find(ep => !hh2._1.pi.contains(Eq(ep._1, ep._2)) && !hh2._1.pi.contains(Not(Eq(ep._1, ep._2)))))
                 yield (hh2, ep)) match {
                 case Some((hh2, ep)) =>
                   hsvisited = hsvisited + ((SymbolicHeap(hh2._1.pi + Eq(ep._1, ep._2), hh2._1.sig), hh2._2))
                   hsvisited = hsvisited + ((SymbolicHeap(hh2._1.pi + Not(Eq(ep._1, ep._2)), hh2._1.sig), hh2._2))
                 case None =>
                   hsvisited = hsvisited + hh2
               }
             }
             case None =>
           }
         }
         hs = hsvisited
       }
     }
    hs
  }

  private def normalise(h1: SymbolicHeap, h2: SymbolicHeap) : Set[(SymbolicHeap, SymbolicHeap)] = {
    val newprop = resolveSpatialConstraints(h1.sig)
    val newh1 = SymbolicHeap(h1.pi ++ newprop, h1.sig)
    satSplit(newh1, h2)
    // NOTICE: Add SAT search phase, hint: consider only operator relevant variables in search
  }


  private def subtract(h1: SymbolicHeap, h2: SymbolicHeap): Boolean = {
    def subfields(rho1: Map[Fields, Expr], rho2: Map[Fields, Expr]): Boolean =
      rho2.forall(p => rho1.contains(p._1) && rho1(p._1) == p._2)
    val newh2 = SymbolicHeap(h2.pi.filterNot {
      case Eq(e1, e2) if e1 == e2 => true
      case e if h1.pi.contains(e) || h1.pi.contains(e.sym) => true // TODO: Support transitivity
      case _ => false
    }, h2.sig) //Remove tautologies and hypotheses
    if (newh2.pi.isEmpty && newh2.sig.isEmpty) h1.sig.isEmpty
    else if (newh2.sig.size > 0 && newh2.sig.size == h1.sig.size)
      newh2.sig.forall(p => h1.sig.contains(p._1) && subfields(h1.sig(p._1).head, p._2.head))
    else false
  }

  def oracle(h1: SymbolicHeap, h2: SymbolicHeap): Boolean = {
    val newhs = normalise(h1, h2)
    newhs.forall(hs => subtract(hs._1, hs._2))
  }
  def incon(h : SymbolicHeap) : Boolean = SymbolicHeapChecker.oracle(h, SymbolicHeap(Set(Not(Eq(Nil(), Nil()))), Map()))

  def allocd(h : SymbolicHeap, e : Expr) : Boolean = {
    incon(SymbolicHeap(h.pi, h.sig.adjust(e) {_ + Map()})) &&
      incon(SymbolicHeap(h.pi + Eq(e, Nil()), h.sig))
  }

}
