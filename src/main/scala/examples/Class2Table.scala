package examples

import testing.TestGenerator
import syntax.PrettyPrinter
import syntax.ast._
import scalaz._, Scalaz._, scalaz.stream._
import scalaz.concurrent.Task
import helper._
import Statement._

object Class2Table extends App {
  val baseClassDefs = Set(
    new ClassDefinition("String", Map(), Map()),
    new ClassDefinition("Int", Map(), Map()),
    new ClassDefinition("Any", Map(), Map()),
    new ClassDefinition("Nothing", Map(), Map())
  )
  val sourceClassDefs = Set(
    new ClassDefinition("Class", Map("attributes" -> ((Class("Attribute"), Many))), Map()),
    new ClassDefinition("Attribute", Map(), Map("type" -> ((Class("String"), Single))))
  )
  val targetClassDefs = Set(
    new ClassDefinition("Table", Map("columns" -> ((Class("Column"), Many))),
      Map("id" -> (Class("IdColumn"), Single))),
    new ClassDefinition("Column", Map(), Map()),
    new ClassDefinition("IdColumn", Map(), Map(), Some(Class("Column"))),
    new ClassDefinition("DataColumn", Map(), Map("type" -> (Class("String"), Single)), Some(Class("Column")))
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
  val tg = new TestGenerator(classDefs.map(cd => Class(cd.name) -> cd).toMap, beta=10, delta=5, kappa=2)
  val task: Task[Unit] = tg.generateTests(Set(pre), prog).map(_.toString).to(io.stdOutLines).run
  task.run
}
