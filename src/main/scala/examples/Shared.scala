package examples

import syntax.ast.ClassDefinition

object Shared {
  val stdClassDefs = Set(
    new ClassDefinition("String", Map(), Map()),
    new ClassDefinition("Int", Map(), Map()),
    new ClassDefinition("Any", Map(), Map())
  )
}
