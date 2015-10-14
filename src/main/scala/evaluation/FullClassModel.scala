package evaluation

import syntax.ast._

object FullClassModel {
  val stdClassDefs = Set(
      new ClassDefinition("Any", Map(), Map())
    , new ClassDefinition("String", Map(), Map(), Class("Any"))
    , new ClassDefinition("Int", Map(), Map(), Class("Any"))
  )
  // TODO Also update diagram with types for method, field and parameter
  val classDefs = Set(
     new ClassDefinition("Package", Map("classes" -> ((Class("Class"), Many()))), Map(), Class("Any"))
    , new ClassDefinition("Class",
                          Map("fields" -> ((Class("Field"), Many())),
                              "methods" -> ((Class("Method"), Many()))),
       Map("super" -> ((Class("Class"), Opt()))), Class("Any")) 
   , new ClassDefinition("Field", Map[Fields, (Class, Cardinality)](),
                         Map("name" -> ((Class("String"), Single())),
                             "type" -> ((Class("Class"), Single()))), Class("Any"))
   , new ClassDefinition("Method", Map("params" -> ((Class("Parameter"), Opt())),
                                        "body" -> ((Class("Statement"), Single()))),
                        Map("name" -> ((Class("String"), Single())),
                            "type" -> ((Class("Class"), Single()))), Class("Any"))
   , new ClassDefinition("Parameter", Map("next" -> ((Class("Parameter"), Opt()))),
                           Map("name" -> ((Class("String"), Single())),
                               "type" -> ((Class("Class"), Single()))), Class("Any"))
   , new ClassDefinition("Statement", Map[Fields, (Class, Cardinality)](),
                           Map[Fields, (Class, Cardinality)](), Class("Any"))
   , new ClassDefinition("Block", Map("current" -> ((Class("Statement"), Single())),
                                      "next" -> ((Class("Statement"), Opt()))),
                         Map[Fields, (Class, Cardinality)](), Class("Statement"))
   , new ClassDefinition("If", Map("then" -> ((Class("Statement"), Single())),
                                   "else" -> ((Class("Statement"), Opt())),
                                   "cond" -> ((Class("Expr"), Single()))),
                               Map[Fields, (Class, Cardinality)](), Class("Statement"))
    , new ClassDefinition("Return", Map("value" -> ((Class("Expr"), Single()))),
                           Map[Fields, (Class, Cardinality)](), Class("Statement"))
    , new ClassDefinition("Assign", Map("left" -> ((Class("AssignableExpr"), Single())),
                                        "right" -> ((Class("Expr"), Single()))),
                           Map[Fields, (Class, Cardinality)](), Class("Statement"))
    , new ClassDefinition("Expr", Map[Fields, (Class, Cardinality)](),
                          Map("type" -> ((Class("Class"), Single()))), Class("Any"))
    , new ClassDefinition("AssignableExpr", Map[Fields, (Class, Cardinality)](),
                          Map[Fields, (Class, Cardinality)](), Class("Expr"))
    , new ClassDefinition("FieldAccessExpr", Map("target" -> ((Class("Expr"), Single()))),
                          Map("field_name" -> ((Class("String"), Single()))),
                          Class("AssignableExpr"))
    , new ClassDefinition("MethodCallExpr", Map("target" -> ((Class("Expr"), Single())),
                                                "args" -> ((Class("Arg"), Opt()))),
                          Map("method_name" -> ((Class("String"), Single())) ), Class("Expr"))

    , new ClassDefinition("Arg", Map("current" -> ((Class("Expr"), Single())),
                                       "next" -> ((Class("Arg"), Opt()))),
                          Map[Fields, (Class, Cardinality)](), Class("Any"))
  )

  val allDefs = stdClassDefs ++ classDefs

  val allDefsWithKeys = allDefs.map(d => Class(d.name) -> d).toMap
}
