package test

import semantics.SymbolicCommandChecker
import syntax.ast.{Skip, SymbolicHeap}

object Application extends App {
  val pre = SymbolicHeap(Set(),Map())
  val c = Skip()
  val post = SymbolicHeap(Set(),Map())
  SymbolicCommandChecker.check(pre, c, post)
}
