package semantics

import syntax.ast._
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

  private val typeInference = new TypeInference(defs)

  private val prelogue =
      List(SetLogic(NonStandardLogic(SSymbol("ALL_SUPPORTED"))))

  private val epilogue = List(CheckSat())

  private def makeScript(subscripts: List[Command]*) =
    Script(prelogue ++ subscripts.fold(List())(_ ++ _) ++ epilogue)

  def isConsistent(heap : syntax.ast.SHeap): Boolean = {
    this.synchronized {
      var interpreter: ScriptInterpreter = null
      try {
        interpreter = ScriptInterpreter(CVCInterpreter.build(CVCInterpreter.defaultArgs ++ Array("--fmf-fun-rlv")))
        val constraintconsistent = checkConstraintConsistency(interpreter, heap)
        //TODO Do QSPatial and pure type constraints as well
        val typeconsistent = checkTypeConsistency(heap)
        constraintconsistent && typeconsistent
      } finally {
          Option(interpreter).map (_.free)
      }
    }
  }

  def checkConstraintConsistency(interpreter : ScriptInterpreter, heap : syntax.ast.SHeap): Boolean = {
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
      case (symid, ConcreteDesc(_, children, _)) =>
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

  def checkTypeConsistency(heap : syntax.ast.SHeap): Boolean = {
    heap.spatial forall {
      case (id, sd) => sd match {
        case AbstractDesc(_) => true
        case ConcreteDesc(c, children, refs) =>
          (children ++ refs).forall {
            case (f, e) =>
              // TODO handle safely
              val (expectedType,_) = defs.fieldType(c, f).get
              val actualType = typeInference.inferType(e, heap)
                actualType == Class("Nothing") ||
                actualType == expectedType   ||
                defs.supertypes(actualType).contains(expectedType)
          }
      }
    }
    type StateCM[A] =  State[Map[syntax.ast.Symbols, Class], A]
    def checkTypeConsistencyBoolExpr(b : BoolExpr) : StateCM[Boolean] = b match {
      case syntax.ast.Not(b) => checkTypeConsistencyBoolExpr(b).map(!_)
      case syntax.ast.And(b1, b2) =>
       for {
         b1c <- checkTypeConsistencyBoolExpr(b1)
         b2c <- checkTypeConsistencyBoolExpr(b2)
       } yield b1c && b2c
      case syntax.ast.ClassMem(e, c) => {
        // TODO handle safely
        val sym = e.asInstanceOf[Symbol]
        val sts = defs.subtypesOrSelf
        for {
          st <- State.get[Map[syntax.ast.Symbols, Class]]
          symtype = if (st.contains(sym.id)) st(sym.id) else SpatialDesc._sd_c.get(heap.spatial(sym.id))
          isSubType = sts(symtype).contains(c)
          _ <- if (isSubType) State.put(st.updated(sym.id, c)) else ().point[StateCM]
        } yield isSubType || defs.supertypes(c).contains(symtype)
      }
      case _ => true.point[StateCM]
    }
    heap.pure.traverseU(checkTypeConsistencyBoolExpr).eval(Map()).forall(identity)
  }

  def makeSSymbol(npref: String, ppref: String, id : syntax.ast.Symbols, symsort : Sort) = {
    (SSymbol(if (id < 0) s"$npref${id.abs}" else s"$ppref$id"), symsort)
  }

  //TODO do proper error handling
  def evalBasicExpr(th: SymbolMap, e: syntax.ast.BasicExpr): Term  = e match {
      case syntax.ast.Symbol(id) => {
        val sym = th(id)
        QualifiedIdentifier(Identifier(sym._1))
      }
      case _ => ???
  }

  def evalSetExpr(th: SymbolMap, e: syntax.ast.SetExpr): Term = e match {
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
    case syntax.ast.SetSymbol(c, id) => {
      val sym = th(id)
      QualifiedIdentifier(Identifier(sym._1))
    }
    case _ => ???
  }

  def evalBoolExpr(th: SymbolMap, b : syntax.ast.BoolExpr): Term = b match {
    case syntax.ast.Eq(e1, e2) => {
      val e1res = evalSetExpr(th, e1)
      val e2res = evalSetExpr(th, e2)
      Equals(e1res, e2res)
    }
    case syntax.ast.ClassMem(e, c) => True() // We don't handle types by the SMT solver
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
    case syntax.ast.True => True()
    case syntax.ast.Not(b) => {
      val bres = evalBoolExpr(th, b)
      Not(bres)
    }
  }

  def evalProp(th: SymbolMap, p : syntax.ast.Prop): List[Term] = {
    val bs = p.foldLeft(List[Term]())((st, b) => {
       val bres = evalBoolExpr(th, b)
       bres :: st
    })
    bs.reverse
   }
}
