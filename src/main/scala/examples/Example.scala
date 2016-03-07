package examples

import helper.Counter
import semantics.ModelFinder
import syntax.ast.{Class,ClassDefinition, Statement}
import semantics.domains._
import testing.{BlackBoxTestGenerator, WhiteBoxTestGenerator}

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
    val defsWithKeys = classDefs.map(cd => Class(cd.name) -> cd).toMap
    val bbtestgenerator = new BlackBoxTestGenerator(defsWithKeys, delta = 5)
    println("""------------ Blackbox test generation -----------------""")
    bbtestgenerator.generateTests(pres).map(_.toString).to(io.stdOutLines).run.run
    println("""-------------------------------------------------------""")
    val wwtestgenerator = new WhiteBoxTestGenerator(defsWithKeys, 2, 5, 2)
    println("""------------ Whitebox test generation -----------------""")
    wwtestgenerator.generateTests(pres, prog).map(_.toString).to(io.stdOutLines).run.run
    println("""-------------------------------------------------------""")
  }
}
