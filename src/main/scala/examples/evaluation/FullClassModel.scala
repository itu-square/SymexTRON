package examples
package evaluation

import syntax.ast._

object FullClassModel {
  val stdClassDefs = Set(
      new ClassDefinition("String", Map(), Map())
    , new ClassDefinition("Int", Map(), Map())
  )
  // TODO Also update diagram with types for method, field and parameter
  val classDefs = Set(
     new ClassDefinition("Package", Map("classes" -> ((Class("Class"), Many))), Map())
    , new ClassDefinition("Class",
                          Map("fields" -> ((Class("Field"), Many)),
                              "methods" -> ((Class("Method"), Many))),
       Map("super" -> ((Class("Class"), Opt)), "name" -> ((Class("String"), Single))))
   , new ClassDefinition("Field", Map[Fields, (Class, Cardinality)](),
                         Map("name" -> ((Class("String"), Single)),
                             "type" -> ((Class("Class"), Single))))
   , new ClassDefinition("Method", Map("params" -> ((Class("Parameter"), Many)),
                                        "body" -> ((Class("Statement"), Single))),
                        Map("name" -> ((Class("String"), Single)),
                            "type" -> ((Class("Class"), Single))))
   , new ClassDefinition("Parameter", Map(),
                           Map("name" -> ((Class("String"), Single)),
                               "type" -> ((Class("Class"), Single))))
   , new ClassDefinition("Statement", Map[Fields, (Class, Cardinality)](), //Abstract
                           Map[Fields, (Class, Cardinality)]())
   , new ClassDefinition("If", Map("then" -> ((Class("Statement"), Single)),
                                   "else" -> ((Class("Statement"), Opt)),
                                   "cond" -> ((Class("Expr"), Single))),
                               Map[Fields, (Class, Cardinality)](), Some(Class("Statement")))
    , new ClassDefinition("Return", Map("value" -> ((Class("Expr"), Single))),
                           Map[Fields, (Class, Cardinality)](), Some(Class("Statement")))
    , new ClassDefinition("Assign", Map("left" -> ((Class("AssignableExpr"), Single)),
                                        "right" -> ((Class("Expr"), Single))),
                           Map[Fields, (Class, Cardinality)](), Some(Class("Statement")))
    , new ClassDefinition("Expr", Map[Fields, (Class, Cardinality)](), // Abstract
                          Map("type" -> ((Class("Class"), Single))))
    , new ClassDefinition("AssignableExpr", Map[Fields, (Class, Cardinality)](),
                          Map[Fields, (Class, Cardinality)](), Some(Class("Expr")))
    , new ClassDefinition("FieldAccessExpr", Map("target" -> ((Class("Expr"), Single))),
                          Map("field_name" -> ((Class("String"), Single))),
                          Some(Class("AssignableExpr")))
    , new ClassDefinition("MethodCallExpr", Map("target" -> ((Class("Expr"), Single)),
                                                "args" -> ((Class("Arg"), Many))),
                          Map("method_name" -> ((Class("String"), Single)) ), Some(Class("Expr")))

    , new ClassDefinition("Arg", Map("value" -> ((Class("Expr"), Single))), Map("name" -> ((Class("String"), Single))))
    , new ClassDefinition("Any", Map(), Map())
    , new ClassDefinition("Nothing", Map(), Map())
  )

  val allDefs = stdClassDefs ++ classDefs

  val allDefsWithKeys = allDefs.map(d => Class(d.name) -> d).toMap
}
