package testing

import syntax.ast._
import syntax.PrettyPrinter
import semantics.{SymbolicExecutor, ConcreteExecutor}
import scalaz._, Scalaz._
import scalaz.stream._
import scalaz.concurrent.Task
import codes.reactive.scalatime._, Scalatime._
import helper._
import codes.reactive.scalatime

class TestGenerator(defs: Map[Class, ClassDefinition],
                    beta: Int, delta: Int, kappa: Int) {
  val symbExec = new SymbolicExecutor(defs, beta, delta, kappa)

  def generateTests(pres : Set[SMem], s : Statement,
        timeout : Duration = TestGenerator.defaultTimeout,
        coverage : Double = TestGenerator.defaultCoverageTarget): Process[Task, CMem] =
    generateTestsE(pres, s, timeout, coverage)
                 .map(_.fold(_ => none, _.some)).filter(_.isDefined).map(_.get)

  def generateTestsE(pres : Set[SMem], s : Statement,
      timeout : Duration = TestGenerator.defaultTimeout,
      coverage : Double = TestGenerator.defaultCoverageTarget): Process[Task, String \/ CMem] = {
    //val concExec = new ConcreteExecutor(defs, s)
    val startTime = LocalTime()
    symbExec.execute(pres, s).map(_.map(_._1)) // Only take initial heaps
            .map(_.flatMap(convertMem))
            .takeWhile(p => LocalTime().isBefore(startTime.plus(timeout))
                      /*  && concExec.branchCoverage <= coverage*/)
  }

  def convertMem(sMem: SMem): String \/ CMem = {
    val maxDepth = 1000
    def sbexpr2sinstance(es : Seq[BasicExpr]) =
      es.map(_.asInstanceOf[Symbol].id).toSet
    def symbolic2concrete(csMem : SMem) =  {
          val cStackr = csMem.stack.toList.traverseU {
            case (x, SetLit(es@_*)) if es.forall(_.isInstanceOf[Symbol]) =>
              (x, sbexpr2sinstance(es)).right
            case (x, e) => s"${PrettyPrinter.pretty(e)} is not a concrete value".left
          }.map(_.toMap)
          val cHeapr = csMem.heap.spatial.toList.traverseU {
            case (symid, ConcreteDesc(c, schildren, srefs)) => {
              for {
                cchildren <- schildren.toList.traverseU {
                  case (f, SetLit(es@_*)) => (f, sbexpr2sinstance(es)).right
                  case (f, e) => s"${PrettyPrinter.pretty(e)} is not a concrete value".left
                }.map(_.toMap)
                crefs <- srefs.toList.traverseU {
                  case (f, SetLit(es@_*)) => (f, sbexpr2sinstance(es)).right
                  case (f, e) => s"${PrettyPrinter.pretty(e)} is not a concrete value".left
                }.map(_.toMap)
              } yield ((symid, c), (symid, cchildren), (symid, crefs))
            }
            case (symid, AbstractDesc(c)) =>
              s"${PrettyPrinter.pretty(Symbol(symid))} is not concrete".left
          }.map(_.unzip3(identity).|> {
            case (tm, chldm, refm) => CHeap(tm.toMap, chldm.toMap, refm.toMap)
          })
          for {
            cStack <- cStackr
            cHeap <- cHeapr
          } yield CMem(cStack, cHeap)
        }

    val allSymbols = SetLit(sMem.heap.spatial.keys.toSet.map(Symbol).toSeq : _*)

    val concreteSMem = symbExec.modelFinder.concretise(allSymbols, sMem, sMem, depth=maxDepth)
               .filter(_.isRight).map(_.toOption.get._2)
               .filter(m => symbExec.heapConsistencyChecker.isConsistent(m.heap))
               .map(symbolic2concrete)
               .take(1).runLast.run
    concreteSMem.cata(identity, s"No concretisation for heap found in depth $maxDepth".left)
  }

}

object TestGenerator {
  val defaultTimeout = 5L.minutes

  val defaultCoverageTarget = 90.0
}
