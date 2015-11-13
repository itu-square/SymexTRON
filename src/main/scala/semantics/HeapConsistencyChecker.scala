package semantics

import syntax.ast._

class HeapConsistencyChecker(defs: Map[Class, ClassDefinition]) {
  import smtlib.parser.Commands._
  import smtlib.parser.Terms._
  import smtlib.parser.CommandsResponses._
  import smtlib.theories.Core._
  import smtlib.theories.Ints._
  import helper.theories.Sets._
  import smtlib.interpreters._
  import helper.interpreters._

  type SymbolMap = Map[syntax.ast.Symbols, (SSymbol, Sort)]

  private val typeSort = Sort(Identifier(SSymbol("Type")))

  object TypeOf extends helper.theories.UnaryOperation { override val name = "typeof" }
  object TypeOfS extends helper.theories.UnaryOperation { override val name = "typeofS" }
  object Subtype extends helper.theories.BinaryOperation { override val name = "subtype" }
  object SubtypeRT extends helper.theories.BinaryOperation { override val name = "subtypeRT" }
  object IsUpperBound extends helper.theories.TernaryOperation { override val name = "isUpperBound" }
  object IsLowerBound extends helper.theories.TernaryOperation { override val name = "isLowerBound" }
  object Lub extends helper.theories.BinaryOperation { override val name = "lub" }
  object Glb extends helper.theories.BinaryOperation { override val name = "glb" }

  private val typeAny     = typeName(Class("Any"))
  private val typeNothing = typeName(Class("Nothing"))
  private def typeName(c : Class) = SSymbol(s"CLASS_${c.name}")

  private val typeTranslations : List[Command] = {
    val sts = defs.subtypes
    val nothing = QualifiedIdentifier(Identifier(typeNothing))
    val any = QualifiedIdentifier(Identifier(typeAny))
    if (defs.isEmpty) List(Assert(Subtype(nothing, any)))
    defs.keys.toList.map(c => DeclareFun(typeName(c), Seq(), typeSort)) ++
      defs.flatMap { ccdef =>
         val (c, cdef) = ccdef
         val cx  = QualifiedIdentifier(Identifier(typeName(c)))
         List(Assert(Subtype(cx, cdef.superclass.fold(any)(sup =>
           QualifiedIdentifier(Identifier(typeName(sup)))
         )))) ++ (if (sts.contains(c) && !sts(c).isEmpty) List()
                 else List(Assert(Subtype(nothing, cx))))
      }
  }

  private val typeDefinitions =
      List(DeclareSort(SSymbol("Type"), 0),
           DeclareFun(SSymbol(TypeOf.name),  Seq(IntSort()), typeSort),
           DeclareFun(SSymbol(TypeOfS.name), Seq(SetSort(IntSort())), typeSort),
           DeclareFun(SSymbol(Subtype.name), Seq(typeSort,typeSort), BoolSort()),
           DeclareFun(SSymbol(SubtypeRT.name), Seq(typeSort,typeSort), BoolSort()),
           DeclareFun(SSymbol(IsUpperBound.name), Seq(typeSort,typeSort,typeSort), BoolSort()),
           DeclareFun(SSymbol(IsLowerBound.name), Seq(typeSort,typeSort,typeSort), BoolSort()),
           DeclareFun(SSymbol(Lub.name), Seq(typeSort,typeSort), typeSort),
           DeclareFun(SSymbol(Glb.name), Seq(typeSort,typeSort), typeSort),
           DeclareFun(typeNothing, Seq(), typeSort ),
           DeclareFun(typeAny,    Seq(), typeSort),
           Assert(Forall(SortedVar(SSymbol("t"), typeSort), Seq(),
            { val t = QualifiedIdentifier(Identifier(SSymbol("t")))
              SubtypeRT(t, t)
            })),
           Assert(Forall(SortedVar(SSymbol("t1"), typeSort),
                    Seq(SortedVar(SSymbol("t2"), typeSort)), {
                         val t1 = QualifiedIdentifier(Identifier(SSymbol("t1")))
                         val t2 = QualifiedIdentifier(Identifier(SSymbol("t2")))
                         Implies(Subtype(t1, t2), SubtypeRT(t1, t2))
                       })),
           Assert(Forall(SortedVar(SSymbol("t1"), typeSort),
                     Seq(SortedVar(SSymbol("t2"), typeSort),
                         SortedVar(SSymbol("t3"), typeSort)), {
                          val t1 = QualifiedIdentifier(Identifier(SSymbol("t1")))
                          val t2 = QualifiedIdentifier(Identifier(SSymbol("t2")))
                          val t3 = QualifiedIdentifier(Identifier(SSymbol("t3")))
                          Implies(And(SubtypeRT(t1, t2), SubtypeRT(t2, t3)),
                                  SubtypeRT(t1, t3))
                        })),
            Assert(Forall(SortedVar(SSymbol("t1"), typeSort),
                      Seq(SortedVar(SSymbol("t2"), typeSort),
                          SortedVar(SSymbol("t3"), typeSort)),
                          {
                            val t1 = QualifiedIdentifier(Identifier(SSymbol("t1")))
                            val t2 = QualifiedIdentifier(Identifier(SSymbol("t2")))
                            val t3 = QualifiedIdentifier(Identifier(SSymbol("t3")))
                            Equals(IsUpperBound(t1,t2,t3),
                                  And(SubtypeRT(t1, t3), SubtypeRT(t2, t3)))
                          })),
            Assert(Forall(SortedVar(SSymbol("t1"), typeSort),
                      Seq(SortedVar(SSymbol("t2"), typeSort),
                          SortedVar(SSymbol("t3"), typeSort)),
                          {
                            val t1 = QualifiedIdentifier(Identifier(SSymbol("t1")))
                            val t2 = QualifiedIdentifier(Identifier(SSymbol("t2")))
                            val t3 = QualifiedIdentifier(Identifier(SSymbol("t3")))
                            Equals(IsLowerBound(t1,t2,t3),
                                  And(SubtypeRT(t3, t1), SubtypeRT(t3, t2)))
                          })),
            Assert(Forall(SortedVar(SSymbol("t1"), typeSort),
                      Seq(SortedVar(SSymbol("t2"), typeSort),
                          SortedVar(SSymbol("t3"), typeSort)),
                          {
                            val t1 = QualifiedIdentifier(Identifier(SSymbol("t1")))
                            val t2 = QualifiedIdentifier(Identifier(SSymbol("t2")))
                            val t3 = QualifiedIdentifier(Identifier(SSymbol("t3")))
                            Equals(Equals(Lub(t1,t2), t3),
                                  And(IsUpperBound(t1,t2,t3),
                                      Forall(SortedVar(SSymbol("t4"), typeSort),
                                             Seq(),
                                             {
                                               val t4 = QualifiedIdentifier(Identifier(SSymbol("t4")))
                                               Implies(IsUpperBound(t1,t2,t4),
                                                       SubtypeRT(t3, t4))
                                             }) ))
                          })),
            Assert(Forall(SortedVar(SSymbol("t1"), typeSort),
                      Seq(SortedVar(SSymbol("t2"), typeSort),
                          SortedVar(SSymbol("t3"), typeSort)),
                          {
                            val t1 = QualifiedIdentifier(Identifier(SSymbol("t1")))
                            val t2 = QualifiedIdentifier(Identifier(SSymbol("t2")))
                            val t3 = QualifiedIdentifier(Identifier(SSymbol("t3")))
                            Equals(Equals(Glb(t1,t2), t3),
                                  And(IsLowerBound(t1,t2,t3),
                                      Forall(SortedVar(SSymbol("t4"), typeSort),
                                             Seq(),
                                             {
                                               val t4 = QualifiedIdentifier(Identifier(SSymbol("t4")))
                                               Implies(IsLowerBound(t1,t2,t4),
                                                       SubtypeRT(t4, t3))
                                             }) ))
                          })),
            Assert({
                    val nothing = QualifiedIdentifier(Identifier(typeNothing))
                    Equals(TypeOfS(EmptySet(SetSort(IntSort()))), nothing)
                  }),
            Assert(Forall(SortedVar(SSymbol("X"), SetSort(IntSort())),
                      Seq(SortedVar(SSymbol("Y"), SetSort(IntSort()))),
                          {
                            val X = QualifiedIdentifier(Identifier(SSymbol("X")))
                            val Y = QualifiedIdentifier(Identifier(SSymbol("Y")))
                            Equals(TypeOfS(Union(X,Y)),
                              Lub(TypeOfS(X), TypeOfS(Y)))
                          })),
            Assert(Forall(SortedVar(SSymbol("X"), SetSort(IntSort())),
                      Seq(SortedVar(SSymbol("Y"), SetSort(IntSort()))),
                          {
                            val X = QualifiedIdentifier(Identifier(SSymbol("X")))
                            val Y = QualifiedIdentifier(Identifier(SSymbol("Y")))
                            Equals(TypeOfS(Intersection(X,Y)),
                              Lub(TypeOfS(X), TypeOfS(Y)))
                          })),
            Assert(Forall(SortedVar(SSymbol("X"), SetSort(IntSort())),
                      Seq(SortedVar(SSymbol("Y"), SetSort(IntSort()))),
                          {
                            val X = QualifiedIdentifier(Identifier(SSymbol("X")))
                            val Y = QualifiedIdentifier(Identifier(SSymbol("Y")))
                            Equals(TypeOfS(Setminus(X,Y)),
                              TypeOfS(X))
                          })),
            Assert(Forall(SortedVar(SSymbol("x"), IntSort()),
                      Seq(SortedVar(SSymbol("X"), SetSort(IntSort()))),
                          {
                            val x = QualifiedIdentifier(Identifier(SSymbol("x")))
                            val X = QualifiedIdentifier(Identifier(SSymbol("X")))
                            Equals(TypeOfS(Insert(Seq(x, X))),
                              Lub(TypeOf(x), TypeOfS(X)))
                          })),
            // Membership
            Assert(Forall(SortedVar(SSymbol("x"), IntSort()),
                      Seq(SortedVar(SSymbol("X"), SetSort(IntSort()))),
                          {
                            val x = QualifiedIdentifier(Identifier(SSymbol("x")))
                            val X = QualifiedIdentifier(Identifier(SSymbol("X")))
                            Implies(Member(x, X),
                              SubtypeRT(TypeOf(x), TypeOfS(X)))
                          }))

            ) ++ typeTranslations

  private val prelogue =
      List(SetOption(ProduceModels(true)),
           SetLogic(NonStandardLogic(SSymbol("AUFLIRAFS"))))

  private val epilogue = List(CheckSat())

  private def makeScript(subscripts: List[Command]*) =
    Script(prelogue ++ subscripts.fold(List())(_ ++ _) ++ epilogue)

  def isConsistent(heap : syntax.ast.SHeap): Boolean = {
    var interpreter: ScriptInterpreter = null
    try {
      interpreter = ScriptInterpreter(CVC4Interpreter.buildDefault)
      val syms = heap.symbols
      val symsmap = syms.map(_.fold(
              ss => (ss.id, makeSSymbol("X", "Y", ss.id, SetSort(IntSort())))
            , s => (s.id, makeSSymbol("x", "y", s.id, IntSort())))).toMap
      val bs = evalProp(symsmap, heap.pure)
      val symsDecl = symsmap.values.toList.map(sym =>
                      DeclareFun(sym._1, Seq(), sym._2) : Command)
      val symsTyping = syms.toList.map(_.fold(
          ss => {
            val cx = QualifiedIdentifier(Identifier(typeName(ss.c._1)))
            val ssym = QualifiedIdentifier(Identifier(symsmap(ss.id)._1))
            Equals(TypeOfS(ssym), cx)
          },
          s => {
            val cx = QualifiedIdentifier(Identifier(typeName(syntax.ast.SpatialDesc._sd_c.get(
              heap.spatial.get(s.id).get))))
            val sym = QualifiedIdentifier(Identifier(symsmap(s.id)._1))
            Equals(TypeOf(sym), cx)
          })).map(Assert(_) : Command)
      val pureConstraints = bs.map(Assert(_) : Command)
      val scr = makeScript(typeDefinitions, symsDecl, symsTyping, pureConstraints)
      val res = interpreter.interpret(scr)
      println(scr)
      println(res)
      interpreter.satStatus(res).fold(false) {
          case SatStatus => true
          case s => println(s);false
      }
    } finally {
        Option(interpreter).map (_.free)
    }
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
    case syntax.ast.ClassMem(e, c) => {
      val eres = evalSetExpr(th, e)
      val cx = QualifiedIdentifier(Identifier(typeName(c)))
      SubtypeRT(TypeOfS(eres), cx)
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
