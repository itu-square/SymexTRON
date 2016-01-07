package syntax.ast

import monocle.{POptional, Lens, PLens, Iso}
import monocle.macros.{GenIso, GenLens, GenPrism}
import monocle.std.tuple2._
import monocle.function.Field2._
import language.higherKinds
import scalaz.{Node => _, _}, Scalaz._
import helper.Counter
import com.codecommit.gll.ast._

trait NAryNode extends com.codecommit.gll.ast.Node {
  import com.codecommit.gll.ast._

  def startSym: Option[scala.Symbol]
  def endSym:   Option[scala.Symbol]
  def sepSym:   Option[scala.Symbol]

  override def form: FormSpec = {
    assert(!children.isEmpty || !startSym.isEmpty, "startSym required when there are no children")
    assert(!(startSym.isEmpty && endSym.isEmpty && sepSym.isEmpty), "at least one of startSym, endSym or sepSym is required")
    if (children.isEmpty) {
      val sf = startSym.get
      endSym.fold[FormSpec](sf)(sf ~ _)
    } else {
      val cf = children.tail.foldLeft[FormSpec](children.head)((fs, n) => fs ~ sepSym.fold[FormSpec](n)(_ ~ n))
      val ef = endSym.fold[FormSpec](cf)(cf ~ _)
      startSym.fold[FormSpec](ef)(_ ~ ef)
    }
  }
}

case class Class(name: String) extends LeafNode // To be defined later

sealed trait Cardinality { def isOptional: Boolean }
case object Single extends Cardinality {
  def isOptional = false
}
case object Many extends Cardinality {
  def isOptional = true
}
case object Opt extends Cardinality {
  def isOptional = true
}

sealed trait ASTType
case object IsSymbolic extends ASTType
case object IsProgram extends ASTType

// We only support single inheritance
case class ClassDefinition(name: String, children: Map[Fields, (Class, Cardinality)],
                           refs: Map[Fields, (Class, Cardinality)], superclass: Option[Class] = None)

sealed trait BasicExpr[T <: ASTType] extends Node
case class Symbol(id: Symbols) extends BasicExpr[IsSymbolic] with LeafNode
case class Var(name: Vars) extends BasicExpr[IsProgram] with LeafNode

sealed trait SetExpr[T <: ASTType] extends Node
case class SetLit[T <: ASTType](es: BasicExpr[T]*) extends SetExpr[T] with NAryNode {
  override val children = es.toList
  override val startSym = 'sl_start.some
  override val endSym   = 'sl_end.some
  override val sepSym   = 'sl_sep.some
}
case class Union[T <: ASTType](e1 : SetExpr[T], e2 : SetExpr[T]) extends SetExpr[T] with BinaryNode {
  override val assocLeft = true
  override val left  = e1
  override val right = e2
  override val sym   = 'union
}
case class Diff[T <: ASTType](e1 : SetExpr[T], e2 : SetExpr[T]) extends SetExpr[T] with BinaryNode {
  override val assocLeft = true
  override val left      = e1
  override val right     = e2
  override val sym       = 'diff
}
case class ISect[T <: ASTType](e1 : SetExpr[T], e2 : SetExpr[T]) extends SetExpr[T] with BinaryNode {
  override val assocLeft = true
  override val left      = e1
  override val right     = e2
  override val sym       = 'isect
}
case class SetVar(name: Vars) extends SetExpr[IsProgram] with LeafNode
case class SetSymbol(c : (Class, Cardinality), id: Symbols) extends SetExpr[IsSymbolic] with LeafNode

sealed trait BoolExpr[T <: ASTType] extends Node
case class Eq[T <: ASTType](e1: SetExpr[T], e2: SetExpr[T]) extends BoolExpr[T] with LeafNode
case class ClassMem(e1: SetExpr[IsSymbolic], s: Class) extends BoolExpr[IsSymbolic] with BinaryNode {
  override val assocLeft = false
  override val left      = e1
  override val right     = s
  override val sym       = 'classmem
}
case class SetMem[T <: ASTType](e1: BasicExpr[T], e2: SetExpr[T]) extends BoolExpr[T] with BinaryNode {
  override val assocLeft = true
  override val left      = e1
  override val right     = e2
  override val sym       = 'setmem
}
case class SetSubEq[T <: ASTType](e1: SetExpr[T], e2: SetExpr[T]) extends BoolExpr[T] with BinaryNode {
  override val assocLeft = true
  override val left      = e1
  override val right     = e2
  override val sym       = 'setsubeq
}
case class And[T <: ASTType](b1: BoolExpr[T], b2: BoolExpr[T]) extends BoolExpr[T] with BinaryNode {
  override val assocLeft = true
  override val left      = b1
  override val right     = b2
  override val sym       = 'and
}
case class True[T <: ASTType]() extends BoolExpr[T] with LeafNode
case class Not[T <: ASTType](b: BoolExpr[T]) extends BoolExpr[T] with UnaryNode {
  override val isPrefix = true
  override val child    = b
  override val sym      = 'not
}

sealed trait MatchExpr
case class MSet(e : SetExpr[IsProgram]) extends MatchExpr
case class Match(e : SetExpr[IsProgram], c : Class) extends MatchExpr
case class MatchStar(e : SetExpr[IsProgram], c : Class) extends MatchExpr

object MatchExpr {
  val _me_e = Lens[MatchExpr, SetExpr[IsProgram]]({
      case MSet(e) => e
      case Match(e, c) => e
      case MatchStar(e, c) => e
    })(newe => {
      case MSet(e) => MSet(newe)
      case Match(e, c) => Match(newe, c)
      case MatchStar(e, c) => MatchStar(newe, c)
    })
}

sealed abstract class SpatialDesc
case class AbstractDesc(c : Class) extends SpatialDesc
case class ConcreteDesc(c : Class, children : Map[Fields, SetExpr[IsSymbolic]], refs : Map[Fields, SetExpr[IsSymbolic]]) extends SpatialDesc

object SpatialDesc {
  val _sd_abstract = GenPrism[SpatialDesc, AbstractDesc]
  val _sd_concrete = GenPrism[SpatialDesc, ConcreteDesc]
  val _sd_c = Lens[SpatialDesc, Class]({ case ConcreteDesc(c, _, _) => c case AbstractDesc(c) => c })(newc => {
    case ConcreteDesc(oldc, chld, refs) => ConcreteDesc(newc, chld, refs)
    case AbstractDesc(oldc) => AbstractDesc(newc)
  })
}

object AbstractDesc {
  val _ad_c = GenLens[AbstractDesc](_.c)
}

object ConcreteDesc {
  val _cd_c = GenLens[ConcreteDesc](_.c)
  val _cd_children = GenLens[ConcreteDesc](_.children)
  val _cd_refs = GenLens[ConcreteDesc](_.refs)
}

case class QSpatial(e : SetExpr[IsSymbolic], c : Class)

object QSpatial {
  val _qs_e = GenLens[QSpatial](_.e)
  val _qs_c = GenLens[QSpatial](_.c)
}

case class QJump(source : SetExpr[IsSymbolic], c : Class, target : SetExpr[IsSymbolic])

object QJump {
  val _qj_source = GenLens[QJump](_.source)
  val _qj_c = GenLens[QJump](_.c)
  val _qj_target = GenLens[QJump](_.target)
}

case class SHeap(spatial: Spatial[Symbols], qspatial: Set[QSpatial], pure : Prop)

object SHeap {
  val _sh_spatial  = GenLens[SHeap](_.spatial)
  val _sh_qspatial = GenLens[SHeap](_.qspatial)
  val _sh_pure     = GenLens[SHeap](_.pure)
}

case class SMem(stack: SStack, heap: SHeap)

object SMem {
  val _sm_stack = GenLens[SMem](_.stack)
  val _sm_heap = GenLens[SMem](_.heap)
}

case class CHeap(typeenv: Map[Instances, Class],
                 childenv: Map[Instances, Map[Fields, Set[Instances]]],
                 refenv: Map[Instances, Map[Fields, Set[Instances]]])

object CHeap {
  val _ch_typeenv  = GenLens[CHeap](_.typeenv)
  val _ch_childenv = GenLens[CHeap](_.childenv)
  val _ch_refenv   = GenLens[CHeap](_.refenv)
}

case class CMem(stack: CStack, heap: CHeap)

object CMem {
  val _cm_stack = GenLens[CMem](_.stack)
  val _cm_heap  = GenLens[CMem](_.heap)
}

case class BranchPoint(stmt_uid: Integer, branch_number: Integer)

sealed trait Statement
case class StmtSeq(metaInf: Statement.MetaInf, ss : Statement*)
  extends Statement
case class AssignVar(metaInf: Statement.MetaInf, x : Vars, e : SetExpr[IsProgram])
  extends Statement
case class LoadField(metaInf: Statement.MetaInf, x : Vars, e : SetExpr[IsProgram], f : Fields)
  extends Statement
case class New(metaInf: Statement.MetaInf, x : Vars, c : Class)
  extends Statement
case class AssignField(metaInf: Statement.MetaInf, e1 : SetExpr[IsProgram], f : Fields, e2 : SetExpr[IsProgram])
  extends Statement
case class If(metaInf: Statement.MetaInf, ds: Statement, cs : (BoolExpr[IsProgram], Statement)*)
  extends Statement
case class For(metaInf: Statement.MetaInf, x: Vars, m: MatchExpr, sb: Statement)
  extends Statement
case class Fix(metaInf: Statement.MetaInf, e : SetExpr[IsProgram], sb: Statement)
  extends Statement

object Statement {
  sealed trait MetaInf
  case class MI(uid: Integer) extends MetaInf
  case object NoMI extends MetaInf

  val _stmt_metaInf = Lens[Statement, MetaInf]({
        case StmtSeq(minf, _*) => minf
        case AssignVar(minf, _, _) => minf
        case LoadField(minf, _, _, _) => minf
        case New(minf, _, _) => minf
        case AssignField(minf, _, _, _) => minf
        case If(minf, _, _*) => minf
        case For(minf, _, _, _) => minf
        case Fix(minf, _, _) => minf
  })(nminf => {
        case StmtSeq(_, ss@_*) => StmtSeq(nminf, ss:_*) // copy doesn't work on list arguments apparently
        case s: AssignVar => s.copy(metaInf = nminf)
        case s: LoadField => s.copy(metaInf = nminf)
        case s: New => s.copy(metaInf = nminf)
        case s: AssignField => s.copy(metaInf = nminf)
        case If(_, ds, cs@_*) => If(nminf, ds, cs:_*) // copy doesn't work on list arguments apparently
        case s: For => s.copy(metaInf = nminf)
        case s: Fix => s.copy(metaInf = nminf)
    })

  private val _stmt_mi = _stmt_metaInf composePrism GenPrism[MetaInf, MI]
  val _stmt_uid = _stmt_mi composeLens GenLens[MI](_.uid)

  def stmtSeq(ss : Statement*) : Statement = StmtSeq(NoMI, ss :_*)
  def assignVar(x : Vars, e : SetExpr[IsProgram]) : Statement = AssignVar(NoMI, x, e)
  def loadField(x : Vars, e : SetExpr[IsProgram], f : Fields) : Statement = LoadField(NoMI, x, e, f)
  def `new`(x : Vars, c : Class) : Statement = New(NoMI, x, c)
  def assignField(e1 : SetExpr[IsProgram], f : Fields, e2 : SetExpr[IsProgram]) : Statement = AssignField(NoMI, e1, f, e2)
  def `if`(ds : Statement, css : (BoolExpr[IsProgram], Statement)*) : Statement = If(NoMI, ds, css :_*)
  def `for`(x : Vars, m : MatchExpr, s : Statement) : Statement = For(NoMI, x, m, s)
  def fix(e : SetExpr[IsProgram], s : Statement) : Statement = Fix(NoMI, e, s)

  def annotateUids(s : Statement) : Statement = {
    val counter = Counter(0)
    def annotateUidH(s : Statement) : Statement = {
      val sMInf = MI(counter.++)
      s match {
        case StmtSeq(_, ss@_*) => StmtSeq(sMInf, ss.map(annotateUidH) :_*)
        case AssignVar(_, x, e) => AssignVar(sMInf, x, e)
        case LoadField(_, x, e, f) => LoadField(sMInf, x, e, f)
        case New(_, x, c) => New(sMInf, x, c)
        case AssignField(_, e1, f, e2) => AssignField(sMInf, e1, f, e2)
        case If(_, ds, cs@_*) => If(sMInf, annotateUidH(ds), cs.map(second[(BoolExpr[IsProgram], Statement), Statement]
                                   .modify(annotateUidH _)) : _*)
        case For(_, x, m, sb) => For(sMInf, x, m, annotateUidH(sb))
        case Fix(_, e, sb) => Fix(sMInf, e, annotateUidH(sb))
      }
    }
    annotateUidH(s)
  }

  def branches(s : Statement) : Map[Integer, List[BranchPoint]] = {
    val uid = _stmt_uid.getOption(s).get
    s match {
      case If(_, ds, cs@_*) => Map(uid ->
              (BranchPoint(uid, 0) :: cs.toList.zipWithIndex.map(p => BranchPoint(uid, p._2 + 1)))) ++
                 cs.map(p => branches(p._2)).fold(Map.empty[Integer, List[BranchPoint]])(_ ++ _)
      // TODO Figure out which branch metric should be used for loops
      case For(_, _, _, sb) => Map(uid -> (for (i <- 0 to 1) yield BranchPoint(uid, i)).toList) ++
                                  branches(sb)
      case Fix(_, _, sb) => Map(uid -> (for (i <- 0 to 1) yield BranchPoint(uid, i)).toList) ++
                                  branches(sb)
      case StmtSeq(_, ss@_*) => ss.map(branches _).fold(Map.empty[Integer, List[BranchPoint]])(_ ++ _)
      case _ => Map(uid -> List())
    }
  }
}
