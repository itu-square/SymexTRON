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
      val fields = (classDef.children.keys ++ classDef.refs.keys).toSet
      val reachedByOwnership = classDef.children.values.map(_.`class`).toSet
      val reachedByRequiredRef = classDef.refs.values.filterNot(_.card.isOptional).map(_.`class`).toSet
      val reachedBySubtyping = defs.subtypes(clazz)
      val classesRelevant = visitedClasses + clazz
      val newTodoClasses: Set[Class] = (todoClasses.tail ++ reachedByOwnership ++ reachedByRequiredRef ++ reachedBySubtyping) diff classesRelevant
      relevantFeatures(newTodoClasses, classesRelevant, relevantFields ++ fields.map(clazz -> _))
    }
  }
  val (relevantClasses, relevantFields) = relevantFeatures(inputTypes, Set[Class](),Set[(Class,Fields)]())
  private val _coveredClasses: TMap[Class, Boolean] = TMap.empty[Class, Boolean]
  private val _coveredFields: TMap[(Class, Fields), Boolean] = TMap.empty[(Class, Fields),Boolean]

  def coveredClasses: Set[Class] = _coveredClasses.snapshot.keySet
  def coveredFields: Set[(Class, Fields)] = _coveredFields.snapshot.keySet

  def coverage: Double = {
    (coveredClasses.size + coveredFields.size) * 100.0 / (relevantClasses.size + relevantFields.size)
  }

  def registerMem(mem: CMem): String \/ Unit = {
    val coveredClasses = mem.heap.typeenv.values.toSet
    val coveredFields =
      mem.heap.typeenv.foldLeft(Set[(Class, Fields)]()) { (st, instinfo) =>
        val (inst, clazz) = instinfo
        def covered(env: Map[Instances, Map[Fields, Set[Instances]]]) : Set[(Class, Fields)] = {
          env.get(inst).cata(_.keySet, Set[Fields]()).map(f => defs.definingClass(clazz, f) -> f)
        }
        st ++ covered(mem.heap.childenv) ++ covered(mem.heap.refenv)
      }
    val irrelevantClasses = coveredClasses diff relevantClasses
    val irrelevantFields  = coveredFields diff relevantFields
    if (irrelevantClasses.nonEmpty) s"Irrelevant classes in mem: ${irrelevantClasses.map(_.name).mkString(",")}".left
    else if (irrelevantFields.nonEmpty) s"Irrelevant fields in mem: ${irrelevantFields.map{case (c,f) => s"$c.$f" }.mkString(",")}".left
    else {
      coveredClasses.foreach { c => atomic { implicit txn => _coveredClasses.update(c, true) } }
      coveredFields.foreach { case (c,f) => atomic { implicit txn => _coveredFields.update((c,f), true) } }
    }.right
  }

}
