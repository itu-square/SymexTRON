package semantics

/*
Based on "Symbolic Execution with Separation Logic" by Berdine et al. (2005)
 */

import syntax.ast._
import Subst._

object SymbolicChecker {
  def check(pre : SymbolicHeap, c : Command, post : SymbolicHeap) : Boolean = {
    if (incon(pre)) true
    else c match {
      case Skip() => oracle(pre, post)
      case AssignVar(x, e, c) =>
        val newx = freshVar()
        val newpre =
          SymbolicHeap(And(Eq(Var(x), e.subst(x, Var(newx))), pre.pi.subst(x, Var(newx))), pre.sig.subst(x, Var(newx)))
        check(newpre, c, post)
      case HeapLookup(x, e, f, c) => ???
      case HeapMutate(e1, f, e2, c) => ???
      case New(x, s, c) => ???
    }
  }

  def freshVar() : Vars = ???

  def oracle(h1: SymbolicHeap, h2: SymbolicHeap): Boolean = ???

  def incon(h : SymbolicHeap) : Boolean = oracle(h, SymbolicHeap(Eq(Nil(), Nil()),Empty()))

  def allocd(h : SymbolicHeap, e : Expr) : Boolean = {
    incon(SymbolicHeap(h.pi, Sep(h.sig, Inst(e, List())))) &&
      incon(SymbolicHeap(And(h.pi, Eq(e, Nil())), h.sig))
  }
}
