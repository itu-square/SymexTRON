package semantics

import helper._
import syntax.PrettyPrinter
import syntax.ast._

import scalaz.\/
import scalaz.\/._

object SymbolicHeapChecker {
  def sortOf(mem: SymbolicMemory, e1: SetExpr): String \/ Sort = mem.heap.pure.find { p =>
    p match {
      case SortMem(e2, s) if e1 == e2 => true
      case _ => false
    }
  }.map(_.asInstanceOf[SortMem].s).fold[String \/ Sort](left(s"Can't find sort of $e1"))(right(_))

  // NOTICE: May need to rerun when having lists/trees or advanced checkers due to guard checks that may become valid
  // Alternatively have a separate phase for non-pointing spatial constraints (list/trees/checkers)
  private def resolveSpatialConstraints(h1: Spatial) : Prop = {
    for (e1 <- h1.keySet)
      yield {
        (for (e2 <- h1.keySet; if e1 != e2)
          yield {
            Not(Eq(e1, e2))
          }) + Not(Eq(e1, SetE()))
      }
  }.flatten

  private def propagatePureConstraints(h1: SymbolicHeap, h2: SymbolicHeap): Option[(SymbolicHeap, SymbolicHeap)] = {
    /*def ppc(pure1 : Prop, spatial1 : Spatial, pure2 : Prop, spatial2 : Spatial, pureh : Prop)
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
    ppc(h1.pure, h1.spatial, h2.pure, h2.spatial, Set())*/
    ???
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
         /*for (hh <- hs) {
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
         }*/
         hs = hsvisited
       }
     }
    hs
  }

  private def normalise(h1: SymbolicHeap, h2: SymbolicHeap) : Set[(SymbolicHeap, SymbolicHeap)] = {
    val newprop = resolveSpatialConstraints(h1.spatial)
    val newh1 = SymbolicHeap(h1.pure ++ newprop, h1.spatial, h1.preds)
    satSplit(newh1, h2)
    // NOTICE: Add SAT search phase, hint: consider only operator relevant variables in search
  }


  private def subtract(h1: SymbolicHeap, h2: SymbolicHeap): Boolean = {
    def subfields(rho1: Map[Fields, SetExpr], rho2: Map[Fields, SetExpr]): Boolean =
      rho2.forall(p => rho1.contains(p._1) && rho1(p._1) == p._2)
    val newh2 = SymbolicHeap(h2.pure /*.filterNot {
      case Eq(e1, e2) if e1 == e2 => true
      case e if h1.pure.contains(e) => true // TODO: Support symmetry transitivity
      case _ => false
    }*/, h2.spatial, h2.preds) //Remove tautologies and hypotheses
    if (newh2.pure.isEmpty && newh2.spatial.isEmpty) h1.spatial.isEmpty
    else if (newh2.spatial.size > 0 && newh2.spatial.size == h1.spatial.size)
      newh2.spatial.forall(p => {
        val (p1fs, p1own) = h1.spatial(p._1).head
        val (p2fs, p2own) = p._2.head
        h1.spatial.contains(p._1) && subfields(p1fs, p2fs) && p1own == p2own
      })
    else false
  }

  def oracle(h1: SymbolicHeap, h2: SymbolicHeap): Boolean = {
    // val newhs = normalise(h1, h2)
    // newhs.forall(hs => subtract(hs._1, hs._2))
    println(s"pre-heap: ${PrettyPrinter.pretty(h1)}\npost-heap: ${PrettyPrinter.pretty(h2)}")
    false
  }

  implicit class SymbolicMemoryHelpers(ls : Set[SymbolicMemory]) {
    def ==>(rs : Set[SymbolicMemory]): SymbolicMemory \/ Unit = {
      val cex = for {
        r <- rs
        if !ls.exists(l => SymbolicHeapChecker.oracle(l.heap, r.heap))
      } yield r
      if (cex.size <= 0) right(())
      else left(cex.head)
    }
  }

  def incon(h : SymbolicHeap) : Boolean =
    SymbolicHeapChecker.oracle(h, SymbolicHeap(Set(Not(Eq(SetE(), SetE()))), h.spatial, h.preds))
}
