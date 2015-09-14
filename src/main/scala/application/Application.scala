package application

import semantics.SymbolicExecutor
import syntax.PrettyPrinter
import syntax.ast._

object Application extends App {
  val sortDefs = Set(
    new SortDefinition("Any", Map(), Map()),
    new SortDefinition("Expr", Map(), Map(), Sort("Any")),
    new SortDefinition("CstI", Map("val" -> Sort("Int")), Map(), Sort("Expr")),
    new SortDefinition("Plus", Map("left" -> Sort("Expr"), "right" -> Sort("Expr")), Map(), Sort("Expr"))
  ).map(sd => Sort(sd.name) -> sd).toMap
  val scc = new SymbolicExecutor(sortDefs)
  val pre = Set(SymbolicMemory(Map(), SymbolicHeap(Set(), Map(), Set())))
  // TODO: Think about aliasing problems
  val prog = CSeq(AssignVar("x", SetE())
                 ,New("y1", Sort("Plus"))
                 ,New("y2", Sort("Plus"))
                 ,AssignVar("x", SetE(Var("y1")))
                 ,New("z", Sort("CstI"))
                 ,AssignField(SetE(Var("x")), "left", SetE(Var("z")))
                 ,LoadField("z", SetE(Var("y1")), "left")
                 ,AssignField(SetE(Var("y2")), "right", SetE(Var("z")))
                 )
  println(s"Resulting heap: ${scc.execute(pre, prog).fold(identity, mems =>
    mems.map(PrettyPrinter.pretty).mkString("\n"))}")
}