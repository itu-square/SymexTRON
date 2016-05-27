package examples

import syntax.ast._


object Shared {
  val stdClassDefs = Set(
    ClassDefinition("String", Map(), Map()),
    ClassDefinition("Int", Map(), Map()),
    ClassDefinition("Any", Map(), Map()),
    ClassDefinition("Empty", Map(), Map(), superclass = Some(Class("String"))),
    ClassDefinition("Concat", Map(), Map("s1" -> FieldDefinition(Class("String"), Req, Ordinary), "s2" -> FieldDefinition(Class("String"), Req, Ordinary)), superclass = Some(Class("String")))
  )
}
