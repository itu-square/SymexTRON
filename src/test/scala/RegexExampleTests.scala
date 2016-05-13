import org.scalatest.{Matchers, FlatSpec}
import semantics.{GarbageCollection, ConcreteExecutor}
import semantics.domains.{CHeap, CMem}
import syntax.ast.Class

/**
  * Created by asal on 13/05/2016.
  */
class RegexAltSimplificationExampleTests extends FlatSpec
  with Matchers {
  import examples.RegexAltSimplification._

  def execFixture = new ConcreteExecutor(classDefs.map(cd => Class(cd.name) -> cd).toMap, prog)

  def retainedVars(mem: CMem) = GarbageCollection.gc(mem, retainvars = Some(Set("regex")))

  "The regular expression alternative simplification example" should "simplify an alternative with two epsilons to an epsilon" in {
    val pre = CMem(Map("regex" -> Set(-1)),
      CHeap(Map(
        -1 -> Class("RegexRef"),
        -2 -> Class("Alt"),
        -3 -> Class("RegexRef"),
        -4 -> Class("RegexRef"),
        -5 -> Class("Epsilon"),
        -6 -> Class("Epsilon")
      ), Map(-1 -> Map("value" -> Set(-2)), -2 -> Map("left" -> Set(-3), "right" -> Set(-4)),
             -3 -> Map("value" -> Set(-5)), -4 -> Map("value" -> Set(-6)),
             -5 -> Map(), -6 -> Map())
       , Map(-1 -> Map(), -2 -> Map(), -3 -> Map(), -4 -> Map(), -5 -> Map(), -6 -> Map())))
    val cex = execFixture
    println(cex.execute(pre).map(retainedVars))
  }

}
