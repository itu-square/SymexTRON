package examples

import semantics.SymbolicExecutor
import syntax.PrettyPrinter
import syntax.ast._
import scalaz._, Scalaz._, scalaz.stream._
import scalaz.concurrent.Task
import helper._
import Statement._

object Class2Table extends App {
  val baseClassDefs = Set(
    new ClassDefinition("String", Map(), Map()),
    new ClassDefinition("Int", Map(), Map())
  )
  val sourceClassDefs = Set(
    new ClassDefinition("Class", Map("attributes" -> ((Class("Attribute"), Many))), Map()),
    new ClassDefinition("Attribute", Map(), Map("type" -> ((Class("String"), Single))))
  )
  val targetClassDefs = Set(
    new ClassDefinition("Table", Map("columns" -> ((Class("Column"), Many))),
      Map("id" -> (Class("IdColumn"), Single))),
    new ClassDefinition("Column", Map(), Map()),
    new ClassDefinition("IdColumn", Map(), Map()),
    new ClassDefinition("DataColumn", Map(), Map("type" -> (Class("String"), Single)))
  )
  val classDefs = baseClassDefs ++ sourceClassDefs ++ targetClassDefs
  val pre = SMem(Map("class" -> SetLit(Symbol(-1))),
                     SHeap(Map(-1 -> ConcreteDesc(Class("Class"),
                           Map("attributes" -> SetSymbol((Class("Attribute"), Many), -2)), Map())),
                           Set(QSpatial(SetSymbol((Class("Attribute"), Many), -2), Class("Attribute"))),
                           Set()))
  val prog = stmtSeq(
    `new`("table", Class("Table")),
    `new`("idcol", Class("IdColumn")),
    assignField(SetLit(Var("table")), "id", SetLit(Var("idcol"))),
    assignField(SetLit(Var("table")), "columns", SetLit(Var("idcol"))),
    `for`("attr", MatchStar(SetLit(Var("class")), Class("Attribute")), stmtSeq(
      `new`("col", Class("DataColumn")),
      loadField("attrtype", SetLit(Var("attr")), "type"),
      assignField(SetLit(Var("col")), "type", SetLit(Var("attrtype"))),
      loadField("tablecolumns", SetLit(Var("table")), "columns"),
      assignField(SetLit(Var("table")), "columns", Union(SetVar("tablecolumns"), SetLit(Var("col"))))
    ))
  )
  val scc = new SymbolicExecutor(classDefs.map(cd => Class(cd.name) -> cd).toMap, beta=1)
  val task: Task[Unit] = scc.execute(Process(pre.right), prog).map(path =>
     path.fold(identity, mem => s"Resulting memory: ${PrettyPrinter.pretty(mem)}")).to(io.stdOutLines).run
  task.run
}
