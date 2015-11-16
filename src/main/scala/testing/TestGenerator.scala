package testing

import syntax.ast._
import semantics.{SymbolicExecutor, ConcreteExecutor}
import scalaz._, Scalaz._
import scalaz.stream._
import scalaz.concurrent.Task
import codes.reactive.scalatime._, Scalatime._

class TestGenerator(defs: Map[Class, ClassDefinition],
                    beta: Int, delta: Int, kappa: Int) {
  val symbExec = new SymbolicExecutor(defs, beta, delta, kappa)

  def generateTests(pres : Set[SMem], s : Statement): Process[Task, CMem] =
    generateTestsE(pres, s).map(_.fold(_ => none, _.some)).filter(_.isDefined).map(_.get)

  def generateTestsE(pres : Set[SMem], s : Statement): Process[Task, String \/ CMem] = {
    val concExec = new ConcreteExecutor(defs, s)
    ???
  }
}

object TestGenerator {
  val defaultTimeout = 5L.minutes

  val defaultCoverageTarget = 90.0
}
