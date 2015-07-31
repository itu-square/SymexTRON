package test

import semantics.SymbolicChecker
import syntax.ast.{Skip, SymbolicHeap}

object Application extends App {
  val pre = SymbolicHeap(Set(),Map())
  val c = Skip()
  val post = SymbolicHeap(Set(),Map())
  SymbolicChecker.check(pre, c, post)
}
