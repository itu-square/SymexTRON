package semantics

/*
Based on "Symbolic Execution with Separation Logic" by Berdine et al. (2005)
 */

import semantics.Subst._
import syntax.ast._

object SymbolicCommandChecker {

  def check(pre : Set[SymbolicMemory], c : Command, post : Set[SymbolicMemory]) : Boolean = {
    // Inconsistent precondition
    if (SymbolicHeapChecker.incon(pre)) true
    else c match {
      case Skip() =>
      case Fail() =>
      case AssignVar(x, e, c) =>
      case Load(x, e, f, c) =>
      case New(x, s, c) =>
      case AssignRef(e1, f, e2, c) =>
      case AssignChild(e1, f, e2, c) =>
      case If(p, cs, c) =>
      case For(x, s, e, inv, cb, c) =>
      case ForMatch(x, s, e, inv, cb, c) =>
    }
  }

  private var symCounter = 0

  private def freshSym(): Symbols = {
    symCounter += 1
    symCounter
  }
}
