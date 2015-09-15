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
  val prog = CSeq(AssignVar("x", SetLit())
                 ,New("y1", Sort("Plus"))
                 ,New("y2", Sort("Plus"))
                 ,AssignVar("x", SetLit(Var("y1")))
                 ,New("z", Sort("CstI"))
                 ,AssignField(SetLit(Var("x")), "left", SetLit(Var("z")))
                 ,LoadField("z", SetLit(Var("y1")), "left")
                 ,AssignField(SetLit(Var("y2")), "right", SetLit(Var("z")))
                 )
  println(s"Resulting heap: ${scc.execute(pre, prog).fold(identity, mems =>
    mems.map(PrettyPrinter.pretty).mkString("\n"))}")
}