package examples


import scala.collection.JavaConversions._

import helper.Counter
import semantics.{PrettyPrinter, DotConverter, ModelFinder}
import syntax.ast.{Class,ClassDefinition, Statement}
import semantics.domains._
import testing.{BlackBoxTestGenerator, WhiteBoxTestGenerator}

import scalaz.concurrent.Task
import scalaz.stream.io


/**
  * Created by asal on 15/01/2016.
  */
trait Example {
  val delta = 8
  val beta = 2
  val kappa = 2

  val pres : Set[SMem]
  val prog : Statement
  val classDefs : Set[ClassDefinition]

  def main(args: Array[String]): Unit = {
    val defsWithKeys = classDefs.map(cd => Class(cd.name) -> cd).toMap
    val bbtestgenerator = new BlackBoxTestGenerator(defsWithKeys, delta = delta)
    println("""------------ Blackbox test generation -----------------""")
    bbtestgenerator.generateTests(pres).map(mem => DotConverter.convertCMem("blackboxmem", mem)).map(_.toString).to(io.stdOutLines).run.run
    println("""-------------------------------------------------------""")
    val wbtestgenerator = new WhiteBoxTestGenerator(defsWithKeys, prog, beta = 2, delta = delta, kappa = 2)
    println("""------------ Whitebox test generation -----------------""")
    wbtestgenerator.generateTests(pres).map(mem => DotConverter.convertCMem("whiteboxmem", mem)).map(_.toString).to(io.stdOutLines).run.run
    println(s"Coverage: ${wbtestgenerator.coverage}")
    println(s"Uncovered branches: ${wbtestgenerator.uncoveredBranches}")
    println(s"Program: ${PrettyPrinter.pretty(wbtestgenerator.annotatedProg)}")
    println("""-------------------------------------------------------""")
  }
}
