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

class WhiteBoxTestGenerator(defs: Map[Class, ClassDefinition], prog: Statement,
                            beta: Int, delta: Int, kappa: Int) {
  private
  val symbExec = new SymbolicExecutor(defs, kappa = kappa, delta = delta, beta = beta)

  private
  val concExec = new ConcreteExecutor(defs, prog)

  private
  implicit val S: ScheduledExecutorService = DefaultScheduler

  def generateTests(pres : Set[SMem], timeout : FiniteDuration = WhiteBoxTestGenerator.defaultTimeout,
                    coverage : Double = WhiteBoxTestGenerator.defaultCoverageTarget): Process[Task, CMem] =
    generateTestsE(pres, timeout, coverage)
                 .map(_.toOption)
                 .filter(_.isDefined).map(_.get)

  def generateTestsE(pres : Set[SMem], timeout : FiniteDuration = WhiteBoxTestGenerator.defaultTimeout,
                     coverage : Double = WhiteBoxTestGenerator.defaultCoverageTarget): Process[Task, String \/ CMem] = {
      // TODO Rewrite using writer monad to be pure
      sleep(timeout).wye(
               symbExec.execute(pres, concExec.prog)
              .map(_.flatMap{ sm => symbExec.modelFinder.concretise(sm) })
              .takeWhile(_ => concExec.coverage <= coverage)
              .map { mem => mem.fold(_ => (), m => { concExec.execute(m); }); mem  }
              )(wye.interrupt)
  }

  def coverage: Int = concExec.coverage
}

object WhiteBoxTestGenerator {
  val defaultTimeout = 10L.minutes

  val defaultCoverageTarget = 95.0
}
