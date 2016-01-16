import org.scalatest._
import syntax.ast._
import semantics._
import examples._
import scalaz._, Scalaz._, scalaz.stream._
import CMem._
import CHeap._

class IntListExampleTests extends FlatSpec
                          with Matchers {

  def execFixture = new ConcreteExecutor(IntListExample.classDefs.map(cd => Class(cd.name) -> cd).toMap,
                                         IntListExample.prog)

  def retainedVars(mem: CMem) = GarbageCollection.retainVars(mem, Set("list", "elem", "containselem"))

  "The int list containment query" should "not find any element in the empty list" in {
    val exec = execFixture
    val pre = CMem(Map("list" -> Set(), "elem" -> Set(-2)), CHeap(Map(-2 -> Class("Int")), Map(-2 -> Map()), Map(-2 -> Map())))
    val expected = _cm_stack.modify(_ + ("containselem" -> Set()))(pre)
    val actual = exec.execute(pre).runLastOr(-\/("no result from execution")).run
    actual should equal (\/-(expected))
  }

  it should "find the element in a singleton list containing only that element" in {
    val exec = execFixture
    val pre = CMem(Map("list" -> Set(-1), "elem" -> Set(-2)),
                   CHeap(Map(-1 -> Class("IntList"),
                             -2 -> Class("Int")),
                         Map(-1 -> Map("next" -> Set()),
                             -2 -> Map(),
                             -3 -> Map()), Map(-1 -> Map("data" -> Set(-2)), -2 -> Map(), -3 -> Map())))
    val expected = (_cm_stack.modify(_ + ("containselem" -> Set(-3))) andThen
                    (_cm_heap ^|-> _ch_typeenv).modify(_ + (-3 -> Class("Any"))))(pre)
    val actual = exec.execute(pre).runLastOr(-\/("no result from execution")).run
    actual.map(retainedVars) should equal (\/-(expected).map(retainedVars))
  }

  it should "not find any element in a singleton list containing only another element" in {
    val exec = execFixture
    val pre = CMem(Map("list" -> Set(-1), "elem" -> Set(-2)),
      CHeap(Map(-1 -> Class("IntList"),
        -2 -> Class("Int"),
        -3 -> Class("Int")),
        Map(-1 -> Map("next" -> Set()),
            -2 -> Map(),
            -3 -> Map()), Map(-1 -> Map("data" -> Set(-3)), -2 -> Map(), -3 -> Map())))
    val expected = (_cm_stack.modify(_ + ("containselem" -> Set(-4))) andThen
      (_cm_heap ^|-> _ch_typeenv).modify(_ + (-4 -> Class("Any"))))(pre)
    val actual = exec.execute(pre).runLastOr(-\/("no result from execution")).run
    actual.map(retainedVars) should equal (\/-(expected).map(retainedVars))
  }
}
