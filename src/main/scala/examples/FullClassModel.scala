package examples

import syntax.ast._

object FullClassModel {
  val classDefs = Set(
      ClassDefinition("Package", Map("classes" -> FieldDefinition(Class("Class"), Many, Ordinary)), Map())
    , ClassDefinition("Class",
                          Map("fields" -> FieldDefinition(Class("Field"), Many, Ordinary),
                              "methods" -> FieldDefinition(Class("Method"), Many, Ordinary)),
       Map("super" -> FieldDefinition(Class("Class"), Opt, Ordinary), "name" -> FieldDefinition(Class("String"), Single, Ordinary)))
   , ClassDefinition("Field", Map(),
                              Map("name" -> FieldDefinition(Class("String"), Single, Ordinary),
                                  "type" -> FieldDefinition(Class("Class"), Single, Ordinary)))
   , ClassDefinition("Method", Map("params" -> FieldDefinition(Class("Parameter"), Many, Ordinary),
                                        "body" -> FieldDefinition(Class("Statement"), Single, Ordinary)),
                        Map("name" -> FieldDefinition(Class("String"), Single, Ordinary),
                            "type" -> FieldDefinition(Class("Class"), Single, Ordinary)))
   , ClassDefinition("Parameter", Map(),
                           Map("name" -> FieldDefinition(Class("String"), Single, Ordinary),
                               "type" -> FieldDefinition(Class("Class"), Single, Ordinary)))
   , ClassDefinition("Statement", Map(), Map())
   , ClassDefinition("If", Map("then" -> FieldDefinition(Class("Statement"), Single, Ordinary),
                               "else" -> FieldDefinition(Class("Statement"), Opt, Ordinary),
                               "cond" -> FieldDefinition(Class("Expr"), Single, Ordinary)),
                               Map(), Some(Class("Statement")))
    , ClassDefinition("Return", Map("value" -> FieldDefinition(Class("Expr"), Single, Ordinary)),
                           Map(), Some(Class("Statement")))
    , ClassDefinition("Assign", Map("left" -> FieldDefinition(Class("AssignableExpr"), Single, Ordinary),
                                    "right" -> FieldDefinition(Class("Expr"), Single, Ordinary)), Map(), Some(Class("Statement")))
    , ClassDefinition("Expr", Map(), Map("type" -> FieldDefinition(Class("Class"), Single, Ordinary)))
    , ClassDefinition("AssignableExpr", Map(), Map(), Some(Class("Expr")))
    , ClassDefinition("FieldAccessExpr", Map("target" -> FieldDefinition(Class("Expr"), Single, Ordinary)),
                          Map("field_name" -> FieldDefinition(Class("String"), Single, Ordinary)),
                          Some(Class("AssignableExpr")))
    , ClassDefinition("MethodCallExpr", Map("target" -> FieldDefinition(Class("Expr"), Single, Ordinary),
                                            "args" -> FieldDefinition(Class("Arg"), Many, Ordinary)),
                          Map("method_name" -> FieldDefinition(Class("String"), Single, Ordinary)), Some(Class("Expr")))

    , ClassDefinition("Arg", Map("value" -> FieldDefinition(Class("Expr"), Single, Ordinary)), Map("name" -> FieldDefinition(Class("String"), Single, Ordinary)))
  )

  val allDefs = Shared.stdClassDefs ++ classDefs
}
