package test

import semantics.SymbolicCommandChecker
import syntax.ast._

object Application extends App {
  val pre = SymbolicHeap(Set(Not(Eq(Var("a"), Var("b")))),Map())
  val c = If(Eq(Var("a"), Var("b")), Fail(), Skip(), Skip()) // New("a", Sort(), New("b", Sort(), Skip()))
  val post = SymbolicHeap(Set(), Map())
  print(s"Verification result: ${SymbolicCommandChecker.check(pre, c, post)}")
}
