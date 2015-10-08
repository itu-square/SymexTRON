package semantics

import syntax.ast._

import scalaz._, scalaz.\/._, Scalaz._

class SemanticAnalysis(defs: Map[Class, ClassDefinition]) {
  def check(state: Map[Vars, Cardinality], stmt: Statement): String \/ Map[Vars, Cardinality] = { ??? }
}
