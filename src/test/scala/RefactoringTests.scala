import org.scalatest._
import syntax.ast._
import semantics._
import evaluation._
import scalaz._, Scalaz._, scalaz.stream._

class RefactoringTests extends FlatSpec with Matchers {
  val symex = new SymbolicExecutor(FullClassModel.allDefsWithKeys, kappa = 2, beta = 5, delta = 7)

  "The rename field refactoring" should "symbolically execute without any error" in {
    val inputmem = Process(Refactoring.renameFieldInput.right)
    val p = symex.execute(inputmem, Refactoring.renameField).exists(_.isRight).runLast.map(_.get)
    p.run shouldBe true
  }
}
