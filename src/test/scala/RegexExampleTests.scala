import org.scalatest.{Matchers, FlatSpec}
import semantics.{GarbageCollection, ConcreteExecutor}
import semantics.domains.CMem
import syntax.ast.Class

/**
  * Created by asal on 13/05/2016.
  */
class RegexAltSimplificationExampleTests extends FlatSpec
  with Matchers {
  import examples.RegexAltSimplification._

  def execFixture = new ConcreteExecutor(classDefs.map(cd => Class(cd.name) -> cd).toMap, prog)

  def retainedVars(mem: CMem) = GarbageCollection.gc(mem)

  //"The regular expression alternative simplification example" should "simplify "

}
