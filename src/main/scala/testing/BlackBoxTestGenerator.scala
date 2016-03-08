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
  // TODO Split ModelFinder into KodKod part and symbolic executor relevant part again
  val modelFinder = new ModelFinder(Counter(0), Counter(0), defs, 0 /*ignore*/, delta, /* ignore*/ false)
  val metamodelcoverage = new MetaModelCoverageChecker(defs)

  private
  def generateCoveringTests(consideredTypes: Set[Class], consideredVars: Set[Vars], constraints: Formula, bounds: Bounds, fieldmap: Map[String, Int], mems: Set[CMem]): Set[CMem] = {
    def gctHelper(mems: Set[CMem], classesUncoverable: Set[Class], fieldsUncoverable: Set[(Class, Fields)]): Set[CMem] = {
      val coverage = metamodelcoverage.relevantPartialCoverage(consideredTypes, mems)
      val additionalClassesToCover = coverage.classesRelevant diff (coverage.classesCovered ++ classesUncoverable)
      val additionalFieldsToCover = coverage.fieldsRelevant diff (coverage.fieldsCovered ++ fieldsUncoverable)
      if (additionalClassesToCover.isEmpty)
        if (additionalFieldsToCover.isEmpty) mems
        else {
          val fieldToCover = additionalFieldsToCover.head
          val fieldConstraint = modelFinder.fieldPresenceConstraint(fieldToCover, fieldmap)
          // TODO Consider encapsulating this in modelFinder instead of unwrapping it and doing all things here
          modelFinder.findSolution(constraints and fieldConstraint, bounds).fold(_ =>
            gctHelper(mems, classesUncoverable, fieldsUncoverable + fieldToCover),
            inst => {
              val nmem = modelFinder.extractConcreteMemory(inst, consideredVars)
              gctHelper(mems, classesUncoverable, fieldsUncoverable)
            }
          )
        }
      else {
        val classToCover = additionalClassesToCover.head
        val classConstraint = modelFinder.classPresenceConstraint(classToCover)
        modelFinder.findSolution(constraints and classConstraint, bounds).fold(_ =>
          gctHelper(mems, classesUncoverable + classToCover, fieldsUncoverable),
          inst => {
            val nmem = modelFinder.extractConcreteMemory(inst, consideredVars)
            gctHelper(mems + nmem, classesUncoverable, fieldsUncoverable)
          }
        )
      }
    }
    gctHelper(mems, Set(), Set())
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
       cc <- modelFinder.concretisationConstraints(pre)
       (constraints, bounds, fieldmap) = cc
       mems = generateCoveringTests(consideredTypes, pre.initStack.keySet, constraints, bounds, fieldmap, Set(startMem))
     } yield mems).fold(_ => Process.empty, mems => Process.emitAll(mems.toSeq))
  }
}
