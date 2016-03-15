package testing

import helper.Counter
import kodkod.ast.Formula
import kodkod.instance.Bounds
import semantics.ModelFinder
import semantics.domains.{UnknownLoc, CMem, SMem}
import _root_.syntax.ast.{Vars, Fields, ClassDefinition, Class}

import scalaz._, Scalaz._
import scalaz.concurrent.Task
import scalaz.stream.{Process0, Process}

/**
  * Created by asal on 02/03/2016.
  */
class BlackBoxTestGenerator(defs: Map[Class, ClassDefinition], delta: Int) {
  val modelFinder = new ModelFinder(defs, delta)
  val metamodelcoverage = new MetaModelCoverageChecker(defs)

  private
  def generateCoveringTests(consideredTypes: Set[Class], pre: SMem, mems: Set[CMem]): Process0[CMem] = {
    def gctHelper(mems: Set[CMem], classesUncoverable: Set[Class], fieldsUncoverable: Set[(Class, Fields)]): Process0[CMem] = {
      val coverage = metamodelcoverage.relevantPartialCoverage(consideredTypes, mems)
      val additionalClassesToCover = coverage.classesRelevant diff (coverage.classesCovered ++ classesUncoverable)
      val additionalFieldsToCover = coverage.fieldsRelevant diff (coverage.fieldsCovered ++ fieldsUncoverable)
      if (additionalClassesToCover.isEmpty)
        if (additionalFieldsToCover.isEmpty) Process()
        else {
          val fieldToCover = additionalFieldsToCover.head
          modelFinder.concretise(pre, fieldsPresent = Set(fieldToCover)).fold(_ =>
            gctHelper(mems, classesUncoverable, fieldsUncoverable + fieldToCover),
            nmem => {
              Process(nmem) ++ gctHelper(mems + nmem, classesUncoverable, fieldsUncoverable)
            }
          )
        }
      else {
        val classToCover = additionalClassesToCover.head
        modelFinder.concretise(pre, classesPresent = Set(classToCover)).fold(_ =>
          gctHelper(mems, classesUncoverable + classToCover, fieldsUncoverable),
          nmem => {
           Process(nmem) ++ gctHelper(mems + nmem, classesUncoverable, fieldsUncoverable)
          }
        )
      }
    }
    Process.emitAll(mems.toSeq) ++ gctHelper(mems, Set(), Set())
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
       mems = generateCoveringTests(consideredTypes, pre, Set(startMem))
     } yield mems).fold(_ => Process.empty, identity)
  }
}
