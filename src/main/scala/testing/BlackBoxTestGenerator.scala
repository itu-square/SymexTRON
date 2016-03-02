package testing

import helper.Counter
import kodkod.ast.Formula
import kodkod.instance.Bounds
import semantics.ModelFinder
import semantics.domains.{UnknownLoc, CMem, SMem}
import syntax.ast.{Fields, ClassDefinition, Class}

import scalaz._, Scalaz._
import scalaz.concurrent.Task
import scalaz.stream.Process

/**
  * Created by asal on 02/03/2016.
  */
class BlackBoxTestGenerator(defs: Map[Class, ClassDefinition], delta: Int) {
  // TODO Split ModelFinder into KodKod part and symbolic executor relevant part again
  val modelFinder = new ModelFinder(Counter(0), Counter(0), defs, 0 /*ignore*/, delta, /* ignore*/ false)
  val metamodelcoverage = new MetaModelCoverageChecker(defs)

  private
  def generateCoveringTests(consideredTypes: Set[Class], constraints: Formula, bounds: Bounds, mems: Set[CMem],
                            classesUncoverable: Set[Class], fieldsUncoverable: Set[(Class, Fields)]): String \/ Set[CMem] = {
    val coverage = metamodelcoverage.relevantPartialCoverage(consideredTypes, mems)
    val additionalClassesToCover = coverage.classesRelevant diff (coverage.classesCovered ++ classesUncoverable)
    val additionalFieldsToCover = coverage.classesRelevant diff (coverage.classesCovered ++ classesUncoverable)
    if (additionalClassesToCover.isEmpty)
      if (additionalFieldsToCover.isEmpty) mems.right
      else ???
    else ???
  }

  def generateTests(pres: Set[SMem]): Process[Task, CMem] = Process.emitAll(pres.toSeq).flatMap[Task, CMem] { pre =>
    val consideredTypes = {
      pre.heap.svltion.values.collect { case UnknownLoc(cl, _, _) => cl } ++
        pre.heap.ssvltion.values.map(_.cl) ++
          pre.heap.currentSpatial.values.map(_.cl) ++
            pre.heap.initSpatial.values.map(_.cl)
    }.toSet
    (for {
       startMem <- modelFinder.concretise(pre)
       (constraints, bounds) <- modelFinder.concretisationConstraints(pre)
       mems <- generateCoveringTests(consideredTypes, constraints, bounds, Set(startMem), Set(), Set())
     } yield mems).fold(_ => Process.empty, mems => Process.emitAll(mems.toSeq))
  }
}
