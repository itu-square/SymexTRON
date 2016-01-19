package examples

import syntax.ast.{Class,ClassDefinition, Statement}
import semantics.domains._
import testing.TestGenerator

import scalaz.concurrent.Task
import scalaz.stream.io


/**
  * Created by asal on 15/01/2016.
  */
trait Example {
  val pres : Set[SMem]
  val prog : Statement
  val classDefs : Set[ClassDefinition]

  def main(args: Array[String]): Unit = {
    val tg = new TestGenerator(classDefs.map(cd => Class(cd.name) -> cd).toMap, beta=10, delta=5, kappa=2)
    val task: Task[Unit] = tg.generateTests(pres, prog).map(_.toString).to(io.stdOutLines).run
    task.run
  }
}
