package examples

import syntax.ast.{Single, Class, ClassDefinition}


object Shared {
  val stdClassDefs = Set(
    ClassDefinition("String", Map(), Map()),
    ClassDefinition("Int", Map(), Map()),
    ClassDefinition("Any", Map(), Map()),
    ClassDefinition("Empty", Map(), Map(), superclass = Some(Class("String"))),
    ClassDefinition("Concat", Map(), Map("left" -> (Class("String"), Single), "right" -> (Class("String"), Single)), superclass = Some(Class("String")))
  )
}
