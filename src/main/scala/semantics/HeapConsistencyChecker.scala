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

  type SymbolMap = Map[syntax.ast.Symbols, (SSymbol, Sort)]

  def isConsistent(heap : syntax.ast.SHeap): Boolean = {
    var interpreter: ScriptInterpreter = null
    try {
      interpreter = ScriptInterpreter(CVC4Interpreter.buildDefault)
      val prelogue =
          List(SetOption(ProduceModels(true)), SetLogic(NonStandardLogic(SSymbol("AUFLIRAFS"))))
      val epilogue = List(CheckSat())
      val (th, bs) = evalProp(Map(), heap.pure)
      val scr = Script(prelogue ++
      th.values.toList.map(sym => DeclareFun(sym._1, Seq(), sym._2) : Command) ++
       bs.map(Assert(_) : Command) ++ epilogue)
      val res = interpreter.interpret(scr)
      interpreter.satStatus(res).fold(false) {
          case SatStatus => true
          case s => false
      }
    } finally {
        Option(interpreter).map (_.free)
    }
  }

  def makeSSymbol(npref: String, ppref: String, id : syntax.ast.Symbols, symsort : Sort) = {
    (SSymbol(if (id < 0) s"$npref${id.abs}" else s"$ppref$id"), symsort)
  }

  //TODO do proper error handling
  def evalBasicExpr(th: SymbolMap, e: syntax.ast.BasicExpr): (SymbolMap, Term)  = e match {
      case syntax.ast.Symbol(id) => {
        val sym = if (th.contains(id)) th(id) else makeSSymbol("x", "y", id, IntSort())
        (th.updated(id, sym), QualifiedIdentifier(Identifier(sym._1)))
      }
      case _ => ???
  }

  def evalSetExpr(th: SymbolMap, e: syntax.ast.SetExpr): (SymbolMap, Term) = e match {
    case syntax.ast.SetLit() => (th, EmptySet(SetSort(IntSort())))
    case syntax.ast.SetLit(es@_*) => {
      val (thr, esres) = es.foldLeft((th, Seq[Term]()))((st, e) => {
        val (th1, eres) = evalBasicExpr(st._1, e)
        (th1, st._2 :+ eres)
      })
      (thr, Insert(esres :+ EmptySet(SetSort(IntSort()))))
    }
    case syntax.ast.Union(e1, e2) => {
      val (th1, e1res) = evalSetExpr(th, e1)
      val (th2, e2res) = evalSetExpr(th1, e2)
      (th2, Union(e1res, e2res))
    }
    case syntax.ast.Diff(e1, e2) => {
      val (th1, e1res) = evalSetExpr(th, e1)
      val (th2, e2res) = evalSetExpr(th1, e2)
      (th2, Setminus(e1res, e2res))
    }
    case syntax.ast.ISect(e1, e2) => {
      val (th1, e1res) = evalSetExpr(th, e1)
      val (th2, e2res) = evalSetExpr(th1, e2)
      (th2, Intersection(e1res, e2res))
    }
    case syntax.ast.SetSymbol(id) => {
      val sym = if (th.contains(id)) th(id) else makeSSymbol("X", "Y", id, SetSort(IntSort()))
      (th.updated(id, sym), QualifiedIdentifier(Identifier(sym._1)))
    }
    case _ => ???
  }

  def evalBoolExpr(th: SymbolMap, b : syntax.ast.BoolExpr): (SymbolMap, Term) = b match {
    case syntax.ast.Eq(e1, e2) => {
      val (th1, e1res) = evalSetExpr(th, e1)
      val (th2, e2res) = evalSetExpr(th1, e2)
      (th2, Equals(e1res, e2res))
    }
    case syntax.ast.ClassMem(e, c) => ???
    case syntax.ast.SetMem(e1, e2) => {
      val (th1, e1res) = evalBasicExpr(th, e1)
      val (th2, e2res) = evalSetExpr(th1, e2)
      (th2, Member(e1res, e2res))
    }
    case syntax.ast.SetSubEq(e1, e2) => {
      val (th1, e1res) = evalSetExpr(th, e1)
      val (th2, e2res) = evalSetExpr(th1, e2)
      (th2, Subset(e1res, e2res))
    }
    case syntax.ast.And(b1, b2) => {
      val (th1, b1res) = evalBoolExpr(th, b1)
      val (th2, b2res) = evalBoolExpr(th1, b2)
      (th2, And(b1res, b2res))
    }
    case syntax.ast.True() => (th, True())
    case syntax.ast.Not(b) => {
      val (th1, bres) = evalBoolExpr(th, b)
      (th1, Not(bres))
    }
  }

  def evalProp(th: SymbolMap, p : syntax.ast.Prop): (SymbolMap, List[Term]) = {
    val (th1, bs) = p.foldLeft((th, List[Term]()))((st, b) => {
       val bres = evalBoolExpr(st._1, b)
       (bres._1, bres._2 :: st._2)
    })
    (th1, bs.reverse)
   }

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
