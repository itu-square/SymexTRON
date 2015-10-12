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
   , new ClassDefinition("Class", Map("fields" -> ((Class("Field"), Many())), "methods" -> ((Class("Method"), Many()))),
                        Map("super" -> ((Class("Class"), Single()))), Class("Any")) // super should be optional
   , new ClassDefinition("Field", Map[Fields, (Class, Cardinality)](),
                             Map("name" -> ((Class("String"), Single())), "type" -> ((Class("Class"), Single()))), Class("Any"))
  )

  val allDefs = stdClassDefs ++ classDefs
}
