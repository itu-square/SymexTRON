package semantics

object HeapConsistencyChecker {
  import smtlib.parser.Commands._
  import smtlib.parser.Terms._
  import smtlib.theories.Ints._
  import helper.theories.Sets._

  def test() {
    val x = QualifiedIdentifier(SimpleIdentifier(SSymbol("x")))
    val y = QualifiedIdentifier(SimpleIdentifier(SSymbol("y")))
    val pf = smtlib.printer.RecursivePrinter.toString(Script(
      List(SetLogic(ALL),
           DeclareFun(SSymbol("x"), Seq(), IntSort()),
           DeclareFun(SSymbol("y"), Seq(), IntSort()),
           Assert(LessThan(NumeralLit(0), Add(x, y))),
           CheckSat()
           ))) //(assert (< 0 (+ x y)))
    print(pf)
  }
}
