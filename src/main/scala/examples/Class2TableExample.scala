package examples

import semantics.domains._
import syntax.ast.Statement._
import syntax.ast._

object Class2TableExample extends Example {

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
  override val pres = Set(SMem(Map("class" -> SetLit(Symbol(-1))),
                     SHeap(Map(-1 ->  SpatialDesc(Class("Class"), ExactDesc,
                                                  Map("attributes" -> SetSymbol(-2)), Map())),
                                                  Set(QSpatial(SetSymbol(-2), Class("Attribute"))),
                                                  Set())))
  override val prog = stmtSeq(
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

}
