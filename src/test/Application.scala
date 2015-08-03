package test

import semantics.SymbolicCommandChecker
import syntax.ast._

object Application extends App {
  val pre = SymbolicHeap(Set(),Map())
  val c = New("a", Sort(), New("b", Sort(), Skip()))
  val post = SymbolicHeap(Set(), Map(Var("a") -> Set(Map()), Var("b") -> Set(Map())))
  print(s"Verification result: ${SymbolicCommandChecker.check(pre, c, post)}")
}
