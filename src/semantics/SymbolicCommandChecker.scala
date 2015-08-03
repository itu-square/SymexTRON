package semantics

/*
Based on "Symbolic Execution with Separation Logic" by Berdine et al. (2005)
 */

import semantics.Subst._
import syntax.ast._

object SymbolicCommandChecker {

  def check(pre : SymbolicHeap, c : Command, post : SymbolicHeap) : Boolean = {
    // Inconsistent precondition
    if (SymbolicHeapChecker.incon(pre)) true
    else c match {
      // Operational rules
      case Skip() => SymbolicHeapChecker.oracle(pre, post)
      case AssignVar(x, e, c) => {
        val newx = freshVar()
        val newpre = pre.subst(x, Var(newx))
        val newpre2 = SymbolicHeap(newpre.pi + Eq(Var(x), e.subst(x, Var(newx))), newpre.sig)
        check(newpre2, c, post)
      }
      case New(x, s, c) => {
        val newx = freshVar()
        val newpre = pre.subst(x, Var(newx))
        val newpre2 = SymbolicHeap(newpre.pi, newpre.sig.updated(Var(x), Set(Map())))
        check(newpre2, c, post)
      }
      case If(p, ct, ce, c) => {
        val newpre1 = SymbolicHeap(pre.pi + p, pre.sig)
        val newpre2 = SymbolicHeap(pre.pi + not(p), pre.sig)
        check(newpre1, ct, post) && check(newpre2, ce, post)
      }
      case HeapLookup(x, e, f, c) if pre.sig.contains(e) && pre.sig(e).size == 1 => {
        val newx = freshVar()
        val (newfs, newe) = lookup(pre.sig(e).head, f)
        val newpre = SymbolicHeap(pre.pi, pre.sig.updated(e, Set(newfs))).subst(x, Var(newx))
        val newpre2 = SymbolicHeap(newpre.pi + Eq(Var(x), newe.subst(x, Var(newx))), newpre.sig)
        check(newpre2,c,post)
      }
      case HeapMutate(e1, f, e2, c) if pre.sig.contains(e1) && pre.sig.size == 1 => {
        val newfs = mutate(pre.sig(e1).head, f, e2)
        val newpre = SymbolicHeap(pre.pi, pre.sig.updated(e1, Set(newfs)))
        check(newpre, c, post)
      }
      // Rearrangement rules
      case Accesses(e) =>
        val othere = pre.sig.find(p => SymbolicHeapChecker.oracle(pre, SymbolicHeap(Set(Eq(e, p._1)), pre.sig)))
        othere match {
          case Some(p) =>
            val newpre = SymbolicHeap(pre.pi, (pre.sig - p._1).updated(e, p._2))
            check(newpre, c, post)
          case None => false
        }
      // No rule applies
      case _ => false
    }
  }

  private var varCounter : Int = 0

  private def freshVar() : Vars = {
    varCounter += 1
    s"__internal__$varCounter"
  }

  private def lookup(fs: Map[Fields, Expr], f: Fields): (Map[Fields, Expr], Expr) =
    if (fs.contains(f)) (fs, fs(f))
    else {
      val newx = freshVar()
      (fs.updated(f, Var(newx)), Var(newx))
    }

  private def mutate(fs: Map[Fields, Expr], f: Fields, e2: Expr) =
    fs.updated(f, e2)
}
