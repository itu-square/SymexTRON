package test

import semantics.SymbolicCommandChecker
import syntax.ast._

object Application extends App {
  val pre = SymbolicHeap(Set(Not(Eq(Nil(), Nil()))),Map())
  val c = Skip()
  val post = SymbolicHeap(Set(),Map())
  SymbolicCommandChecker.check(pre, c, post)
}
