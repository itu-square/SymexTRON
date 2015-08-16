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
            NotEq(e1, e2)
          }) + NotEq(e1, Nil())
      }
  }.flatten

  private def propagatePureConstraints(h1: SymbolicHeap, h2: SymbolicHeap): Option[(SymbolicHeap, SymbolicHeap)] = {
    def ppc(pure1 : Prop, spatial1 : Spatial, pure2 : Prop, spatial2 : Spatial, pureh : Prop)
            : Option[(SymbolicHeap, SymbolicHeap)] = {
      if (pure1.size <= 0) Some (SymbolicHeap(pureh, spatial1), SymbolicHeap(pure2, spatial2))
      else pure1.head match {
        case Eq(e1, e2) if e1 == e2 => ppc(pure1.tail, spatial1, pure2, spatial2, pureh)
        case Eq(Symbol(x), e2) =>
          ppc(pure1.tail.subst(x, e2), spatial1.subst(x, e2), pure2.subst(x, e2), spatial2.subst(x, e2), pureh.subst(x, e2))
        case Eq(e1, Symbol(x)) =>
          ppc(pure1.tail.subst(x, e1), spatial1.subst(x, e1), pure2.subst(x, e1), spatial2.subst(x, e1), pureh.subst(x, e1))
        case NotEq(e1, e2) if e1 == e2 => None
        case p => ppc(pure1.tail, spatial1, pure2, spatial2, pureh + p)
      }
    }
    ppc(h1.pure, h1.spatial, h2.pure, h2.spatial, Set())
  }

  private def propagateConstraints(h1: SymbolicHeap, h2: SymbolicHeap): Option[(SymbolicHeap, SymbolicHeap)] = {
    for (hh <- propagatePureConstraints(h1, h2);
         if hh._1.spatial.find(p => p._2.size != 1).isEmpty) //Ensure that all spatial elements are defined at most once
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
               val es = (hh2._1.freevars ++ hh2._2.freevars).map[Expr, Set[Expr]](Symbol(_)) + Nil()
               val eps = for (e1 <- es; e2 <- es; if e1 != e2) yield (e1, e2)
               (for (ep <- eps.find(ep => !hh2._1.pure.contains(Eq(ep._1, ep._2))
                                                 && !hh2._1.pure.contains(NotEq(ep._1, ep._2))))
                 yield (hh2, ep)) match {
                 case Some((hh2, ep)) =>
                   hsvisited = hsvisited + ((SymbolicHeap(hh2._1.pure + Eq(ep._1, ep._2), hh2._1.spatial), hh2._2))
                   hsvisited = hsvisited + ((SymbolicHeap(hh2._1.pure + NotEq(ep._1, ep._2), hh2._1.spatial), hh2._2))
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
    val newprop = resolveSpatialConstraints(h1.spatial)
    val newh1 = SymbolicHeap(h1.pure ++ newprop, h1.spatial)
    satSplit(newh1, h2)
    // NOTICE: Add SAT search phase, hint: consider only operator relevant variables in search
  }


  private def subtract(h1: SymbolicHeap, h2: SymbolicHeap): Boolean = {
    def subfields(rho1: Map[Fields, Expr], rho2: Map[Fields, Expr]): Boolean =
      rho2.forall(p => rho1.contains(p._1) && rho1(p._1) == p._2)
    val newh2 = SymbolicHeap(h2.pure.filterNot {
      case Eq(e1, e2) if e1 == e2 => true
      case e if h1.pure.contains(e) || h1.pure.contains(e.sym) => true // TODO: Support transitivity
      case _ => false
    }, h2.spatial) //Remove tautologies and hypotheses
    if (newh2.pure.isEmpty && newh2.spatial.isEmpty) h1.spatial.isEmpty
    else if (newh2.spatial.size > 0 && newh2.spatial.size == h1.spatial.size)
      newh2.spatial.forall(p => h1.spatial.contains(p._1) && subfields(h1.spatial(p._1).head, p._2.head))
    else false
  }

  def oracle(h1: SymbolicHeap, h2: SymbolicHeap): Boolean = {
    // val newhs = normalise(h1, h2)
    // newhs.forall(hs => subtract(hs._1, hs._2))
    println(s"pre-heap: $h1, post-heap: $h2")
    true
  }
  def incon(h : SymbolicHeap) : Boolean =
    SymbolicHeapChecker.oracle(h, SymbolicHeap(Set(NotEq(Nil(), Nil())), Map()))
}
