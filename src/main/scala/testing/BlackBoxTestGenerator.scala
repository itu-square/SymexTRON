package testing

import helper.Counter
import kodkod.ast.Formula
import kodkod.instance.Bounds
import semantics.ModelFinder
import semantics.domains.{UnknownLoc, CMem, SMem}
import _root_.syntax.ast.{Vars, Fields, ClassDefinition, Class}

import scalaz._, Scalaz._
import scalaz.concurrent.Task
import scalaz.stream.Process

/**
  * Created by asal on 02/03/2016.
  */
class BlackBoxTestGenerator(defs: Map[Class, ClassDefinition], delta: Int) {
  val modelFinder = new ModelFinder(defs, delta)
  val metamodelcoverage = new MetaModelCoverageChecker(defs)

  private
  def generateCoveringTests(consideredTypes: Set[Class], pre: SMem, mems: Set[CMem]): Set[CMem] = {
    def gctHelper(mems: Set[CMem], classesUncoverable: Set[Class], fieldsUncoverable: Set[(Class, Fields)]): Set[CMem] = {
      println(s"gctHelper($mems, $classesUncoverable, $fieldsUncoverable)")
      val coverage = metamodelcoverage.relevantPartialCoverage(consideredTypes, mems)
      val additionalClassesToCover = coverage.classesRelevant diff (coverage.classesCovered ++ classesUncoverable)
      val additionalFieldsToCover = coverage.fieldsRelevant diff (coverage.fieldsCovered ++ fieldsUncoverable)
      if (additionalClassesToCover.isEmpty)
        if (additionalFieldsToCover.isEmpty) mems
        else {
          val fieldToCover = additionalFieldsToCover.head
          modelFinder.concretise(pre, fieldsPresent = Set(fieldToCover)).fold(_ =>
            gctHelper(mems, classesUncoverable, fieldsUncoverable + fieldToCover),
            nmem => {
              gctHelper(mems + nmem, classesUncoverable, fieldsUncoverable)
            }
          )
        }
      else {
        val classToCover = additionalClassesToCover.head
        modelFinder.concretise(pre, classesPresent = Set(classToCover)).fold({err =>
          println(err)
          gctHelper(mems, classesUncoverable + classToCover, fieldsUncoverable)},
          nmem => {
            gctHelper(mems + nmem, classesUncoverable, fieldsUncoverable)
          }
        )
      }
    }
    gctHelper(mems, Set(), Set())
  }

  def generateTests(pres: Set[SMem]): Process[Task, CMem] = Process.emitAll(pres.toSeq).flatMap[Task, CMem] { pre =>
    val consideredTypes = {
      pre.heap.svltion.values.collect { case UnknownLoc(cl, _) => cl } ++
        pre.heap.ssvltion.values.map(_.cl) ++
          pre.heap.currentSpatial.values.map(_.cl) ++
            pre.heap.initSpatial.values.map(_.cl)
    }.toSet
    (for {
       startMem <- modelFinder.concretise(pre)
       mems = generateCoveringTests(consideredTypes, pre, Set(startMem))
     } yield mems).fold(_ => Process.empty, mems => Process.emitAll(mems.toSeq))
  }
}
