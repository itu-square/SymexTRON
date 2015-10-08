package examples

import semantics.SymbolicExecutor
import syntax.PrettyPrinter
import syntax.ast._

object RunningExample extends App {
  val baseClassDefs = Set(
    new ClassDefinition("Any", Map(), Map()),
    new ClassDefinition("String", Map(), Map(), Class("Any")),
    new ClassDefinition("Int", Map(), Map(), Class("Any"))
  )
  val sourceClassDefs = Set(
    new ClassDefinition("Class", Map("attributes" -> (Class("Attribute"), Single())), Map(), Class("Any")),
    new ClassDefinition("Attribute", Map(), Map(), Class("Any"))
  )
  val targetClassDefs = Set(
    new ClassDefinition("Table", Map("columns" -> (Class("Column"), Many())),
      Map("id" -> (Class("IdColumn"), Single())), Class("Any")),
    new ClassDefinition("Column", Map(), Map(), Class("Any")),
    new ClassDefinition("IdColumn", Map(), Map(), Class("Column")),
    new ClassDefinition("DataColumn", Map(), Map("type" -> (Class("String"), Single())), Class("Column"))
  )
  val classDefs = baseClassDefs ++ sourceClassDefs ++ targetClassDefs
  val pre = Set(SMem(Map("class" -> SetLit(Symbol(-1))),
                     SHeap(Map(-1 -> ConcreteDesc(Class("Class"), Map("attributes" -> SetSymbol(-2)), Map())),
                           Set(QSpatial(SetSymbol(-2), Class("Attribute"), SetLit())),
                           Set())))
  val prog = StmtSeq(
    New("table", Class("Table")),
    New("idcol", Class("IdColumn")),
    AssignField(SetLit(Var("table")), "id", SetLit(Var("idcol"))),
    AssignField(SetLit(Var("table")), "columns", SetLit(Var("idcol"))) /*,
    For("attr", MatchStar(SetLit(Var("class")), Class("Attribute")), StmtSeq(
      New("col", Class("DataColumn")),
      LoadField("attrtype", SetLit(Var("attr")), "type"),
      AssignField(SetLit(Var("col")), "type", SetLit(Var("attrtype"))),
      LoadField("tablecolumns", SetLit(Var("table")), "columns"),
      AssignField(SetLit(Var("table")), "columns", Union(SetVar("tablecolumns"), SetLit(Var("col"))))
    ))*/
  )
  val scc = new SymbolicExecutor(classDefs.map(cd => Class(cd.name) -> cd).toMap)
  println(s"Resulting memory: ${scc.execute(pre, prog).fold(identity, mems =>
    mems.map(PrettyPrinter.pretty).mkString("\n"))}")
}