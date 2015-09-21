package application

import semantics.SymbolicExecutor
import syntax.PrettyPrinter
import syntax.ast._

object Application extends App {
  val sortDefs = Set(
    new ClassDefinition("Any", Map(), Map()),
    new ClassDefinition("Expr", Map(), Map(), Class("Any")),
    new ClassDefinition("CstI", Map("val" -> Class("Int")), Map(), Class("Expr")),
    new ClassDefinition("Plus", Map("left" -> Class("Expr"), "right" -> Class("Expr")), Map(), Class("Expr"))
  ).map(sd => Class(sd.name) -> sd).toMap
  val scc = new SymbolicExecutor(sortDefs)
  val pre = Set(SMem(Map(), SHeap(Set(), Map(), Set())))
  // TODO: Think about aliasing problems
  val prog = StmtSeq(AssignVar("x", SetLit())
                 ,New("y1", Class("Plus"))
                 ,New("y2", Class("Plus"))
                 ,AssignVar("x", SetLit(Var("y1")))
                 ,New("z", Class("CstI"))
                 ,AssignField(SetLit(Var("x")), "left", SetLit(Var("z")))
                 ,LoadField("z", SetLit(Var("y1")), "left")
                 ,AssignField(SetLit(Var("y2")), "right", SetLit(Var("z")))
                 )
  println(s"Resulting heap: ${scc.execute(pre, prog).fold(identity, mems =>
    mems.map(PrettyPrinter.pretty).mkString("\n"))}")
}