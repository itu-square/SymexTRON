package examples

import semantics.domains._
import syntax.ast.Statement._
import syntax.ast._

trait Class2TableExample extends Example {

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
  override val classDefs = Shared.stdClassDefs ++ sourceClassDefs ++ targetClassDefs

  override val pres = {
    val stack = Map("class" -> SetLit(Seq(Symbol(-1))))
    Set(
      SMem(stack, stack,
        SHeap.initial(Map(), Map(Symbol(-1) -> UnknownLoc(Class("Class"), SUnowned, Set())), Map(), Map(), Set()))
    )
  }

}

object Class2TableSimpleExample extends Class2TableExample {
  override val prog = stmtSeq(
    `new`("table", Class("Table")),
    `new`("idcol", Class("IdColumn")),
    assignField(Var("table"), "id", Var("idcol")),
    assignField(Var("table"), "columns", Var("idcol")),
    loadField("class_attributes", Var("class"), "attributes"),
    `for`("attr", MSet(Var("class_attributes")), stmtSeq(
      `new`("col", Class("DataColumn")),
      loadField("attrtype", Var("attr"), "type"),
      assignField(Var("col"), "type", Var("attrtype")),
      loadField("tablecolumns", Var("table"), "columns"),
      assignField(Var("table"), "columns", Union(Var("tablecolumns"), Var("col")))
    ))
  )
}

object Class2TableDeepMatchingExample extends Class2TableExample {
  override val prog = stmtSeq(
    `new`("table", Class("Table")),
    `new`("idcol", Class("IdColumn")),
    assignField(Var("table"), "id", Var("idcol")),
    assignField(Var("table"), "columns", Var("idcol")),
    `for`("attr", MatchStar(Var("class"), Class("Attribute")), stmtSeq(
      `new`("col", Class("DataColumn")),
      loadField("attrtype", Var("attr"), "type"),
      assignField(Var("col"), "type", Var("attrtype")),
      loadField("tablecolumns", Var("table"), "columns"),
      assignField(Var("table"), "columns", Union(Var("tablecolumns"), Var("col")))
    ))
  )
}