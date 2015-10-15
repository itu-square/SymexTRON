import org.scalatest._
import syntax.ast._
import semantics._
import evaluation._
import scalaz._, Scalaz._, scalaz.stream._

class RefactoringTests extends FlatSpec with Matchers {
  val symex = new SymbolicExecutor(FullClassModel.allDefsWithKeys, kappa = 2, beta = 5, delta = 7)

  "The rename field refactoring" should "symbolically execute without any error" in {
    val packageId        = -1
    val classId          = -2
    val oldFieldId       = -3
    val newFieldId       = -4
    val packageClassesId = -5
    val classFieldsId    = -6
    val classMethodsId   = -7
    val classNameId      = -8
    val classSuperId     = -9

    val inputStack = Map("package" -> SetLit(Symbol(packageId)), "class" -> SetLit(Symbol(classId)),
                         "old_field" -> SetLit(Symbol(oldFieldId)), "new_field" -> SetLit(Symbol(newFieldId)))
    val inputHeap = SHeap(Map(packageId ->
                                ConcreteDesc(Class("Package"),
                                             Map("classes" -> Union(SetSymbol(packageClassesId), SetLit(Symbol(classId)))),
                                             Map[Fields, SetExpr]()),
                              classId ->
                                ConcreteDesc(Class("Class"),
                                             Map("fields" -> Union(SetSymbol(classFieldsId), SetLit(Symbol(oldFieldId))),
                                                 "methods" -> SetSymbol(classMethodsId))
                                            , Map("name" -> SetLit(Symbol(classNameId)),
                                                  "super" -> SetSymbol(classSuperId))),
                               oldFieldId -> AbstractDesc(Class("Field"), SetLit()),
                               newFieldId -> AbstractDesc(Class("Field"), SetLit())),
                          Set(QSpatial(SetSymbol(packageClassesId), Class("Class"), SetLit()),
                              QSpatial(SetSymbol(classFieldsId), Class("Field"), SetLit()),
                              QSpatial(SetSymbol(classMethodsId), Class("Method"), SetLit())),
                          Set())
    val inputMem = Process(SMem(inputStack, inputHeap).right)
    val p = symex.execute(inputMem, Refactoring.renameField).exists(_.isRight).runLast.map(_.get)
    p.run shouldBe true
  }
}
