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
              .map(_.flatMap{ sm => symbExec.modelFinder.concretise(sm) })
              .takeWhile(_ => concExec.coverage <= coverage)
              .map { mem => mem.fold(_ => (), m => { concExec.execute(m);  println(s"Test coverage: ${concExec.coverage}"); () }); mem }
              .onComplete { println(s"Test coverage: ${concExec.coverage}"); Process() }
              )(wye.interrupt)
  }
}

object WhiteBoxTestGenerator {
  val defaultTimeout = 10L.minutes

  val defaultCoverageTarget = 95.0
}
