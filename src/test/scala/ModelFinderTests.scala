import examples.Class2TableSimpleExample
import kodkod.ast.{Variable, Formula}
import kodkod.instance.{Bounds, Instance}
import org.scalatest.{FlatSpec, Matchers, PrivateMethodTester}
import semantics.ModelFinder
import syntax.ast.Class

import scalaz.{\/, \/-}

/**
  * Created by asal on 11/03/2016.
  */
class ModelFinderTests extends FlatSpec
  with Matchers
  with PrivateMethodTester {
  def execFixture = new ModelFinder(Class2TableSimpleExample.classDefs.map(cd => Class(cd.name) -> cd).toMap, 3)

  val concretisationConstraints = PrivateMethod[String \/ (Formula, Bounds, Map[String, Int])]('concretisationConstraints)
  val classPresenceConstraint = PrivateMethod[Formula]('classPresenceConstraint)
  val findSolution = PrivateMethod[String \/ Instance]('findSolution)

  "The model finder" should "find an instance with an attribute for the class-to-table transformation" in {
    val modelFinder = execFixture
    val ccr = modelFinder invokePrivate concretisationConstraints(Class2TableSimpleExample.pres.head)
    ccr should be a 'right
    ccr match {
      case \/-((constraints, bounds, fieldmap)) =>
        val attrPresent = modelFinder invokePrivate classPresenceConstraint(Class("Attribute"))
        val solr = modelFinder invokePrivate findSolution(constraints and attrPresent, bounds)
        solr should be a 'right
      case _ =>
    }
  }
}
