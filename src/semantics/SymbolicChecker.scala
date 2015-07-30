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
        val newpre = pre.subst(x, Var(newx))
        val newpre2 = SymbolicHeap(And(Eq(Var(x), e.subst(x, Var(newx))), newpre.pi), newpre.sig)
        check(newpre2, c, post)
      case New(x, s, c) =>
        val newx = freshVar()
        val newpre = pre.subst(x, Var(newx))
        val newpre2 = SymbolicHeap(newpre.pi, Sep(Inst(Var(newx), Map()),newpre.sig))
        check(newpre2, c, post)
      case If(p, ct, ce, c) =>
        val newpre1 = SymbolicHeap(And(p, pre.pi), pre.sig)
        val newpre2 = SymbolicHeap(And(Not(p), pre.pi), pre.sig)
        check(newpre1, ct, post) && check(newpre2, ce, post)
      case HeapLookup(x, e, f, c) => ???
      case HeapMutate(e1, f, e2, c) => ???
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
