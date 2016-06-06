package semantics

import semantics.domains.{CMem, Instances}
import _root_.syntax.ast._

import scala.concurrent.stm._
import scalaz.Scalaz._
import scalaz._

/**
  * Created by asal on 01/03/2016.
  */
class MetaModelCoverageChecker(defs: Map[Class, ClassDefinition], inputTypes: Set[Class]) {

  def relevantFeatures(todoClasses: Set[Class],
                       visitedClasses: Set[Class],
                       relevantFields: Set[(Class, Fields)]): (Set[Class], Set[(Class, Fields)])  = {
    if (todoClasses.isEmpty) (visitedClasses, relevantFields)
    else {
      val clazz = todoClasses.head
      val classDef = defs(clazz)
      val fields = (classDef.children.keys ++ classDef.refs.filterNot {case (f, fd) => fd.fieldtype == Tracking} .keys).toSet
      val reachedByOwnership = classDef.children.values.map(_.`class`).toSet
      val reachedByRequiredRef = classDef.refs.values.filterNot(_.card.isOptional).map(_.`class`).toSet
      val reachedBySubtyping = defs.subtypes(clazz)
      val classesRelevant = visitedClasses + clazz
      val newTodoClasses: Set[Class] = (todoClasses.tail ++ reachedByOwnership ++ reachedByRequiredRef ++ reachedBySubtyping) diff classesRelevant
      relevantFeatures(newTodoClasses, classesRelevant, relevantFields ++ fields.map(clazz -> _))
    }
  }
  val (relevantClasses, relevantFields) = {
    val (rc, rf) = relevantFeatures(inputTypes, Set[Class](),Set[(Class,Fields)]())
    (rc.filterNot(c => defs(c).isAbstract), rf)
  }
  private val _coveredClasses: TMap[Class, Boolean] = TMap.empty[Class, Boolean]
  private val _coveredFields: TMap[(Class, Fields), Boolean] = TMap.empty[(Class, Fields),Boolean]

  def coveredClasses: Set[Class] = _coveredClasses.snapshot.keySet
  def coveredFields: Set[(Class, Fields)] = _coveredFields.snapshot.keySet

  def coverage: Double = {
    ((relevantClasses intersect coveredClasses).size + (relevantFields intersect coveredFields).size) * 100.0 / (relevantClasses.size + relevantFields.size)
  }

  def registerMem(mem: CMem): Unit = {
    val mem_ = GarbageCollection.gc(mem)
    val coveredClasses = mem_.heap.typeenv.values.toSet
    val coveredFields =
      mem_.heap.typeenv.foldLeft(Set[(Class, Fields)]()) { (st, instinfo) =>
        val (inst, clazz) = instinfo
        def covered(env: Map[Instances, Map[Fields, Set[Instances]]]) : Set[(Class, Fields)] = {
          env.get(inst).toSet.flatMap(_.toSet[(Fields, Set[Instances])].flatMap[(Class, Fields), Set[(Class, Fields)]] { case (f, os) => if (os.nonEmpty) Set(defs.definingClass(clazz, f) -> f) else Set() })
        }
        st ++ covered(mem_.heap.childenv) ++ covered(mem_.heap.refenv)
      }
    coveredClasses.foreach { c => atomic { implicit txn => _coveredClasses.update(c, true) } }
    coveredFields.foreach { case (c,f) => atomic { implicit txn => _coveredFields.update((c,f), true) } }
  }

}
