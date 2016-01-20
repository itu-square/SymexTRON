package semantics

import syntax.ast._
import semantics.domains._
import scalaz.State, scalaz.syntax.applicative._
import helper._

class HeapConsistencyChecker(defs: Map[Class, ClassDefinition]) {
  import smtlib.parser.Commands._
  import smtlib.parser.Terms._
  import smtlib.parser.CommandsResponses._
  import smtlib.theories.Core._
  import smtlib.theories.Ints._
  import helper.theories.Sets._
  import helper.theories._
  import smtlib.interpreters._
  import helper.interpreters._

  object Distinct extends NAryOperation { override val name = "distinct" }

  type SymbolMap = Map[syntax.ast.Symbols, (SSymbol, Sort)]

  private val prelogue =
      List(SetLogic(NonStandardLogic(SSymbol("ALL_SUPPORTED"))))

  private val epilogue = List(CheckSat())

  private def makeScript(subscripts: List[Command]*) =
    Script(prelogue ++ subscripts.fold(List())(_ ++ _) ++ epilogue)

  def isConsistent(heap : semantics.domains.SHeap): Boolean = {
    this.synchronized {
      var interpreter: ScriptInterpreter = null
      try {
        interpreter = ScriptInterpreter(CVCInterpreter.build(CVCInterpreter.defaultArgs))
        checkConstraintConsistency(interpreter, heap)
      } finally {
          Option(interpreter).map (_.free)
      }
    }
  }

  def checkConstraintConsistency(interpreter : ScriptInterpreter, heap : semantics.domains.SHeap): Boolean = {
    val syms = heap.symbols
    val symsmap = syms.map(_.fold(
            ss => (ss.id, makeSSymbol("X", "Y", ss.id, SetSort(IntSort())))
          , s => (s.id, makeSSymbol("x", "y", s.id, IntSort())))).toMap
    val bs = evalProp(symsmap, heap.pure)
    val symsDecl = symsmap.values.toList.map(sym =>
                    DeclareFun(sym._1, Seq(), sym._2) : Command)
    val pureConstraints = bs.map(Assert(_) : Command)
    val separation =
       if (heap.spatial.size >= 2)
         List(Assert(Distinct(heap.spatial.keys.toSeq
                       .map(symsmap).map {
                         case (ssym, _) => QualifiedIdentifier(Identifier(ssym))
                       })))
      else List()
    val directAcyclicity = heap.spatial.collect {
      case (symid, SpatialDesc(_, _, children, _)) =>
        children.values.toList.map(e =>
            Assert(Not(Member(
              QualifiedIdentifier(Identifier(symsmap(symid)._1)),
              evalSetExpr(symsmap, e))))
        )
    }.toList.flatten
    val scr = makeScript(symsDecl, separation, directAcyclicity, pureConstraints)
    val res = interpreter.interpret(scr)
    interpreter.satStatus(res).fold(false) {
        case SatStatus => true
        case s => false
    }
  }

  def makeSSymbol(npref: String, ppref: String, id : syntax.ast.Symbols, symsort : Sort) = {
    (SSymbol(if (id < 0) s"$npref${id.abs}" else s"$ppref$id"), symsort)
  }

  //TODO do proper error handling
  def evalBasicExpr(th: SymbolMap, e: syntax.ast.BasicExpr[IsSymbolic.type]): Term  = e match {
      case syntax.ast.Symbol(id) => {
        val sym = th(id)
        QualifiedIdentifier(Identifier(sym._1))
      }
  }

  def evalSetExpr(th: SymbolMap, e: syntax.ast.SetExpr[IsSymbolic.type]): Term = e match {
    case syntax.ast.SetLit() => EmptySet(SetSort(IntSort()))
    case syntax.ast.SetLit(es@_*) => {
      val esres = es.foldLeft(EmptySet(SetSort(IntSort()))){ (st, e) =>
        val eres = evalBasicExpr(th, e)
        Insert(Seq(eres, st))
      }
      esres
    }
    case syntax.ast.Union(e1, e2) => {
      val e1res = evalSetExpr(th, e1)
      val e2res = evalSetExpr(th, e2)
      Union(e1res, e2res)
    }
    case syntax.ast.Diff(e1, e2) => {
      val e1res = evalSetExpr(th, e1)
      val e2res = evalSetExpr(th, e2)
      Setminus(e1res, e2res)
    }
    case syntax.ast.ISect(e1, e2) => {
      val e1res = evalSetExpr(th, e1)
      val e2res = evalSetExpr(th, e2)
      Intersection(e1res, e2res)
    }
    case syntax.ast.SetSymbol(id) => {
      val sym = th(id)
      QualifiedIdentifier(Identifier(sym._1))
    }
  }

  def evalBoolExpr(th: SymbolMap, b : syntax.ast.BoolExpr[IsSymbolic.type]): Term = b match {
    case syntax.ast.Eq(e1, e2) => {
      val e1res = evalSetExpr(th, e1)
      val e2res = evalSetExpr(th, e2)
      Equals(e1res, e2res)
    }
    case syntax.ast.SetMem(e1, e2) => {
      val e1res = evalBasicExpr(th, e1)
      val e2res = evalSetExpr(th, e2)
      Member(e1res, e2res)
    }
    case syntax.ast.SetSubEq(e1, e2) => {
      val e1res = evalSetExpr(th, e1)
      val e2res = evalSetExpr(th, e2)
      Subset(e1res, e2res)
    }
    case syntax.ast.And(b1, b2) => {
      val b1res = evalBoolExpr(th, b1)
      val b2res = evalBoolExpr(th, b2)
      And(b1res, b2res)
    }
    case syntax.ast.True() => True()
    case syntax.ast.Not(b) => {
      val bres = evalBoolExpr(th, b)
      Not(bres)
    }
  }

  def evalProp(th: SymbolMap, p : semantics.domains.Prop): List[Term] = {
    val bs = p.foldLeft(List[Term]())((st, b) => {
       val bres = evalBoolExpr(th, b)
       bres :: st
    })
    bs.reverse
   }
}
