package semantics

object HeapConsistencyChecker {
  import smtlib.parser.Commands._
  import smtlib.parser.Terms._
  import smtlib.parser.CommandsResponses._
  import smtlib.theories.Core._
  import smtlib.theories.Ints._
  import helper.theories.Sets._
  import smtlib.interpreters._
  import helper.interpreters._

  def test() {
    var interpreter: ScriptInterpreter = null
    try {
      interpreter = ScriptInterpreter(CVC4Interpreter.buildDefault)
      val x = QualifiedIdentifier(SimpleIdentifier(SSymbol("x")))
      val y = QualifiedIdentifier(SimpleIdentifier(SSymbol("y")))
      val z = QualifiedIdentifier(SimpleIdentifier(SSymbol("z")))
      val pf = Script(
        List(SetOption(ProduceModels(true)),
             SetLogic(NonStandardLogic(SSymbol("AUFLIRAFS"))),
             DeclareFun(SSymbol("x"), Seq(), SetSort(IntSort())),
             DeclareFun(SSymbol("y"), Seq(), SetSort(IntSort())),
             DeclareFun(SSymbol("z"), Seq(), SetSort(IntSort())),
             Assert(Equals(z, Union(x, y))),
             Assert(Not(Equals(z, y))),
             //Assert(Not(Equals(z, x))),
             Assert(Subset(z, x)),
             CheckSat()
             )) //(assert (< 0 (+ x y)))
      print(smtlib.printer.RecursivePrinter.toString(pf))
      val res = interpreter.interpret(pf)
      interpreter.satStatus(res).fold(println(res)) {
        case SatStatus => interpreter.getModel.fold(println("no model"))(print)
        case s => println(s)
      }
    } finally {
      Option(interpreter).map (_.free)
    }
  }
}
