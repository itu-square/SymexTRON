package testing

import semantics.{SymbolicExecutor, SetNormalizer, ConcreteExecutor, PrettyPrinter}
import semantics.domains._

import syntax.ast._
import scalaz._, Scalaz._
import scalaz.stream._, scalaz.stream.time._
import scala.concurrent.duration._
import scalaz.concurrent.Task
import java.util.concurrent.ScheduledExecutorService
import helper._

class WhiteBoxTestGenerator(defs: Map[Class, ClassDefinition],
                            beta: Int, delta: Int, kappa: Int) {
  val symbExec = new SymbolicExecutor(defs, beta, delta, kappa)

  implicit val S: ScheduledExecutorService = DefaultScheduler

  def generateTests(pres : Set[SMem], s : Statement,
                    timeout : FiniteDuration = WhiteBoxTestGenerator.defaultTimeout,
                    coverage : Double = WhiteBoxTestGenerator.defaultCoverageTarget): Process[Task, CMem] =
    generateTestsE(pres, s, timeout, coverage)
                 .map(_.fold(_ => none, _.some))
                 .filter(_.isDefined).map(_.get)

  def generateTestsE(pres : Set[SMem], s : Statement,
                     timeout : FiniteDuration = WhiteBoxTestGenerator.defaultTimeout,
                     coverage : Double = WhiteBoxTestGenerator.defaultCoverageTarget): Process[Task, String \/ CMem] = {
      val concExec = new ConcreteExecutor(defs, s)
      // TODO Rewrite using writer monad to be pure
      sleep(timeout).wye(
               symbExec.execute(pres, concExec.prog)
              .map(_.fold(err => err.left, sm => convertMem(sm)))
              .takeWhile(_ => concExec.branchCoverage <= coverage)
              .map { mem => mem.fold(_ => (), m => { concExec.execute(m);  println(s"Test coverage: ${concExec.branchCoverage}"); () }); mem }
              .onComplete { println(s"Test coverage: ${concExec.branchCoverage}"); Process() }
              )(wye.interrupt)
  }

  def convertMem(sMem: SMem): String \/ CMem = { CMem(Map(),CHeap(Map(), Map(), Map())).right } /* ??? {
    val maxDepth = 3
    def sbexpr2sinstance(es : Seq[BasicExpr[IsSymbolic.type]]) =
      es.map { case Symbol(ident) => ident }.toSet
    def symbolic2concrete(csMem : SMem): (String, String) \/ CMem =  {
          val cStackr = csMem.stack.toList.traverseU {
            case (x, SetLit(es@_*)) if es.forall(_.isInstanceOf[Symbol]) =>
              (x, sbexpr2sinstance(es)).right
            case (x, e) => (PrettyPrinter.pretty(csMem), s"${PrettyPrinter.pretty(e)} is not a concrete value").left
          }.map(_.toMap)
          val cHeapr = csMem.heap.spatial.toList.traverseU {
            case (symid, SpatialDesc(c, ExactDesc,schildren, srefs)) => {
              for {
                cchildren <- schildren.toList.traverseU {
                  case (f, SetLit(es@_*)) => (f, sbexpr2sinstance(es)).right
                  case (f, e) => (PrettyPrinter.pretty(csMem), s"${PrettyPrinter.pretty(e)} is not a concrete value").left
                }.map(_.toMap)
                crefs <- srefs.toList.traverseU {
                  case (f, SetLit(es@_*)) => (f, sbexpr2sinstance(es)).right
                  case (f, e) => (PrettyPrinter.pretty(csMem), s"${PrettyPrinter.pretty(e)} is not a concrete value").left
                }.map(_.toMap)
              } yield ((symid, c), (symid, cchildren), (symid, crefs))
            }
            case (symid, _) =>
              (PrettyPrinter.pretty(csMem), s"${PrettyPrinter.pretty(Symbol(symid))} is not concrete").left
          }.map(_.unzip3(identity).|> {
            case (tm, chldm, refm) => CHeap(tm.toMap, chldm.toMap, refm.toMap)
          })
          for {
            cStack <- cStackr
            cHeap <- cHeapr
          } yield CMem(cStack, cHeap)
        }

    val allSymbols = sMem.heap.spatial.keys.toSet

    val concreteSMem = symbExec.modelFinder.concretise(allSymbols, sMem, sMem, alsoReferences = true, depth=maxDepth)
               .filter(_.isRight).map(_.toOption.get._2)
               .filter(m => symbExec.heapConsistencyChecker.isConsistent(m.heap))
               .map(symbolic2concrete)
               .take(1).runLast.run
    concreteSMem.cata(identity, (PrettyPrinter.pretty(sMem), s"No concretisation for heap found in depth $maxDepth").left)
  } */

}

object WhiteBoxTestGenerator {
  val defaultTimeout = 1L.minutes

  val defaultCoverageTarget = 95.0
}
