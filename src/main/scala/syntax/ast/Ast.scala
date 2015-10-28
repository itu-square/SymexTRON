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
case class Single() extends Cardinality {
  def isOptional = false
}
case class Many() extends Cardinality {
  def isOptional = true
}
case class Opt() extends Cardinality {
  def isOptional = true
}

case class ClassDefinition(name: String, children: Map[Fields, (Class, Cardinality)],
                           refs: Map[Fields, (Class, Cardinality)], supers: Class*)

sealed trait BasicExpr extends Node
case class Symbol(id: Symbols) extends BasicExpr with LeafNode
case class Var(name: Vars) extends BasicExpr with LeafNode

sealed trait SetExpr extends Node
case class SetLit(es: BasicExpr*) extends SetExpr with NAryNode {
  override val children = es.toList
  override val startSym = 'sl_start.some
  override val endSym   = 'sl_end.some
  override val sepSym   = 'sl_sep.some
}
case class Union(e1 : SetExpr, e2 : SetExpr) extends SetExpr with BinaryNode {
  override val assocLeft = true
  override val left  = e1
  override val right = e2
  override val sym   = 'union
}
case class Diff(e1 : SetExpr, e2 : SetExpr) extends SetExpr with BinaryNode {
  override val assocLeft = true
  override val left      = e1
  override val right     = e2
  override val sym       = 'diff
}
case class ISect(e1 : SetExpr, e2 : SetExpr) extends SetExpr with BinaryNode {
  override val assocLeft = true
  override val left      = e1
  override val right     = e2
  override val sym       = 'isect
}
case class SetVar(name: Vars) extends SetExpr with LeafNode
case class SetSymbol(id: Symbols) extends SetExpr with LeafNode

sealed trait BoolExpr extends Node
case class Eq(e1: SetExpr, e2: SetExpr) extends BoolExpr with LeafNode
case class ClassMem(e1: SetExpr, s: Class) extends BoolExpr with BinaryNode {
  override val assocLeft = false
  override val left      = e1
  override val right     = s
  override val sym       = 'classmem
}
case class SetMem(e1: BasicExpr, e2: SetExpr) extends BoolExpr with BinaryNode {
  override val assocLeft = true
  override val left      = e1
  override val right     = e2
  override val sym       = 'setmem
}
case class SetSub(e1: SetExpr, e2: SetExpr) extends BoolExpr with BinaryNode {
  override val assocLeft = true
  override val left      = e1
  override val right     = e2
  override val sym       = 'setsub
}
case class SetSubEq(e1: SetExpr, e2: SetExpr) extends BoolExpr with BinaryNode {
  override val assocLeft = true
  override val left      = e1
  override val right     = e2
  override val sym       = 'setsubeq
}
case class And(b1: BoolExpr, b2: BoolExpr) extends BoolExpr with BinaryNode {
  override val assocLeft = true
  override val left      = b1
  override val right     = b2
  override val sym       = 'and
}
case class True() extends BoolExpr with LeafNode
case class Not(b: BoolExpr) extends BoolExpr with UnaryNode {
  override val isPrefix = true
  override val child    = b
  override val sym      = 'not
}

sealed trait MatchExpr
case class MSet(e : SetExpr) extends MatchExpr
case class Match(e : SetExpr, c : Class) extends MatchExpr
case class MatchStar(e : SetExpr, c : Class) extends MatchExpr

object MatchExpr {
  val _me_e = Lens[MatchExpr, SetExpr]({
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
case class AbstractDesc(c : Class, unowned : SetExpr) extends SpatialDesc
case class ConcreteDesc(c : Class, children : Map[Fields, SetExpr], refs : Map[Fields, SetExpr]) extends SpatialDesc

object SpatialDesc {
  val _sd_abstract = GenPrism[SpatialDesc, AbstractDesc]
  val _sd_concrete = GenPrism[SpatialDesc, ConcreteDesc]
  val _sd_c = Lens[SpatialDesc, Class]({ case ConcreteDesc(c, _, _) => c case AbstractDesc(c, _) => c })(newc => {
    case ConcreteDesc(oldc, chld, refs) => ConcreteDesc(newc, chld, refs)
    case AbstractDesc(oldc, unowned) => AbstractDesc(newc, unowned)
  })
}

object AbstractDesc {
  val _ad_c = GenLens[AbstractDesc](_.c)
  val _ad_unowned = GenLens[AbstractDesc](_.unowned)
}

object ConcreteDesc {
  val _cd_c = GenLens[ConcreteDesc](_.c)
  val _cd_children = GenLens[ConcreteDesc](_.children)
  val _cd_refs = GenLens[ConcreteDesc](_.refs)
}

case class QSpatial(e : SetExpr, c : Class, unowned : SetExpr)

object QSpatial {
  val _qs_e = GenLens[QSpatial](_.e)
  val _qs_c = GenLens[QSpatial](_.c)
  val _qs_unowned = GenLens[QSpatial](_.unowned)
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
case class AssignVar(metaInf: Statement.MetaInf, x : Vars, e : SetExpr)
  extends Statement
case class LoadField(metaInf: Statement.MetaInf, x : Vars, e : SetExpr, f : Fields)
  extends Statement
case class New(metaInf: Statement.MetaInf, x : Vars, c : Class)
  extends Statement
case class AssignField(metaInf: Statement.MetaInf, e1 : SetExpr, f : Fields, e2 : SetExpr)
  extends Statement
case class If(metaInf: Statement.MetaInf, ds: Statement, cs : (BoolExpr, Statement)*)
  extends Statement
case class For(metaInf: Statement.MetaInf, x: Vars, m: MatchExpr, sb: Statement)
  extends Statement
case class Fix(metaInf: Statement.MetaInf, e : SetExpr, sb: Statement)
  extends Statement

object Statement {
  sealed trait MetaInf
  case class MI(uid: Integer) extends MetaInf
  case class NoMI() extends MetaInf

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

  def stmtSeq(ss : Statement*) : Statement = StmtSeq(NoMI(), ss :_*)
  def assignVar(x : Vars, e : SetExpr) : Statement = AssignVar(NoMI(), x, e)
  def loadField(x : Vars, e : SetExpr, f : Fields) : Statement = LoadField(NoMI(), x, e, f)
  def `new`(x : Vars, c : Class) : Statement = New(NoMI(), x, c)
  def assignField(e1 : SetExpr, f : Fields, e2 : SetExpr) : Statement = AssignField(NoMI(), e1, f, e2)
  def `if`(ds : Statement, css : (BoolExpr, Statement)*) : Statement = If(NoMI(), ds, css :_*)
  def `for`(x : Vars, m : MatchExpr, s : Statement) : Statement = For(NoMI(), x, m, s)
  def fix(e : SetExpr, s : Statement) : Statement = Fix(NoMI(), e, s)

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
        case If(_, ds, cs@_*) => If(sMInf, ds, cs.map(second[(BoolExpr, Statement), Statement].modify(annotateUidH _)) : _*)
        case For(_, x, m, sb) => For(sMInf, x, m, sb)
        case Fix(_, e, sb) => Fix(sMInf, e, sb)
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
