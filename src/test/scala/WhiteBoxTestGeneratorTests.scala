import org.scalatest.{Matchers, FlatSpec}
import semantics.domains.SMem
import syntax.ast.{Class, ClassDefinition, Statement}
import testing.WhiteBoxTestGenerator
import examples._

import scalaz.concurrent.Task
import scalaz.stream.Process

/**
  * Created by asal on 15/03/2016.
  */
class WhiteBoxTestGeneratorTests
  extends FlatSpec
  with Matchers {

  def testGenerator(defs: Set[ClassDefinition], prog: Statement) = new WhiteBoxTestGenerator(defs.map(cd => Class(cd.name) -> cd).toMap, prog, beta = 2, delta = 8, kappa = 2)

  def coverageTarget(tg: WhiteBoxTestGenerator, pres: Set[SMem], target: Int): Unit = {
    tg.generateTests(pres).run[Task].run
    tg.coverage should equal(target)
  }

  def run(example: Example, target: Int) = {
    import example._
    val tg = testGenerator(classDefs, prog)
    coverageTarget(tg, pres, target)
  }

  "The whitebox test generator" should "generate 100% covering tests for simple sequential program" in {
    run(SimpleBoxSequentialLoadingExample, 100)
  }

  it should "generate 100% covering tests for simple branching-loading program" in {
    run(SimpleBoxBranchingLoadingExample, 100)
  }

  it should "generate 100% covering tests for simple loading-branching program" in {
    run(SimpleBoxLoadingBranchingExample, 100)
  }

  it should "generate 100% covering tests for simple iteration program" in {
    run(IdIterExample, 100)
  }

  it should "generate 100% covering tests for int list containment query program" in {
    run(IntListContainsElementExample, 100)
  }

  it should "generate 100% covering tests for int list head-tail equivalence program" in {
    run(IntListHeadTailEqExample, 100)
  }

  it should "generate 100% covering tests for class-to-table transformation with simple for-loop" in {
    run(Class2TableSimpleExample, 100)
  }

  it should "generate 100% covering tests for class-to-table transformation with deep matching for-loop" in {
    run(Class2TableDeepMatchingExample, 100)
  }

  it should "generate 100% covering tests for blog post timestamp query program" in {
    run(BlogPostFeedTimestampsExample, 100)
  }

  it should "generate 100% covering tests for blog post capitalize title transformation" in {
    run(BlogPostFeedCapitaliseTitlesExample, 100)
  }
}
