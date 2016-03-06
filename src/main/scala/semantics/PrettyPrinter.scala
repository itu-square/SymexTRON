package semantics

import domains._
import syntax.ast._

object PrettyPrinter {

  def pretty(stack: SStack): String = s"[${stack.map {case (vr, e) => s"${vr} ↦ ${pretty(e)}"}.mkString(", ")}]"

  private val symbs = "αβγδεζηθικλμνξοxπρςστυφχψω"

  private def prettySymb(ident : Int) : String = {
    val l = symbs.length
    val j = {
      val j = ident % l
      if (j < 0) j + l else j
    }
    val i = ident / l
    s"${symbs(j)}${if (ident >= 0) if (i == 0) "" else s"`$i" else "´"}"
  }

  def pretty[T <: ASTType](e : BasicExpr[T]): String = {
    e match {
      case Symbol(ident) => prettySymb(ident)
      case Var(name) => name
    }
  }

  def pretty[T <: ASTType](e : SetExpr[T]): String = {
    e match {
      case SetSymbol(ident) => s"${prettySymb(ident).toUpperCase}"
      case SetVar(name) => name
      case SetLit(es) => if (es.length <= 0) "∅" else s"{${es.map(pretty[T]).mkString(", ")}}"
      case Union(e1, e2) => s"(${pretty(e1)} ∪ ${pretty(e2)})"
      case Diff(e1, e2) => s"(${pretty(e1)} ∖ ${pretty(e2)})"
      case ISect(e1, e2) => s"(${pretty(e1)} ∩ ${pretty(e2)})"
    }
  }

  def pretty[T <: ASTType](sp: BoolExpr[T]): String = sp match {
    case Eq(e1, e2) => s"(${pretty(e1)} = ${pretty(e2)})"
    case SetMem(e1, e2) => s"(${pretty(e1)} ∈ ${pretty(e2)})"
    case SetSubEq(e1, e2) => s"(${pretty(e1)} ⊆ ${pretty(e2)})"
    case True() => "true"
    case And(e1, e2) => s"(${pretty(e1)} ∧ ${pretty(e2)})"
    case Not(p) => p match {
      case Eq(e1, e2) => s"(${pretty(e1)} ≠ ${pretty(e2)})"
      case SetMem(e1, e2) => s"(${pretty(e1)} ∉ ${pretty(e2)})"
      case SetSubEq(e1, e2) => s"(${pretty(e1)} ⊈ ${pretty(e2)})"
      case True() => "false"
      case And(e1@Not(_), e2@Not(_))
         => s"(${pretty(e1)} ∨ ${pretty(e2)})"
      case And(e1, e2) => s"¬(${pretty(e1)} ∧ ${pretty(e2)})"
      case Not(be) => s"${pretty(be)}"
    }
  }

  def pretty(pure: Prop): String = pure.map(pretty[IsSymbolic.type]).mkString(" ∧ ")

  def pretty(loc : Loc, spatialDesc: SpatialDesc): String = spatialDesc match {
    case SpatialDesc(c, typ, children, refs, descendantspool) => {
      // TODO Pretty descendant pool
      val prettytyp = typ match {
        case ExactDesc => s"${pretty(loc)} : ${c.name}"
        case AbstractDesc => s"inst${c.name}〉${pretty(loc)}"
        case PartialDesc(hasExact, possible) => s"inst〈${sep(if (hasExact) s"☐${c.name}" else "", ",", possible.map(_.name).mkString(", "))}〉 ${pretty(loc)}"
      }
      sep(prettytyp, "★",
        sep(s"${children.map{ case (f, e) => pretty(loc, f, "◆↣", e) }.mkString(" ★ ")}", "★",
          s"${refs.map{ case (f, e) => pretty(loc, f, "↝", e) }.mkString(" ★ ")}"))
    }
  }

  def pretty[T <: ASTType](sym : Symbols, f : Fields, sep : String, e : SetExpr[T]): String =
    s"${pretty(Symbol(sym))}.$f $sep ${pretty(e)}"

  def pretty(loc: Loc): String = s"⟪${loc.id}⟫"

  def pretty(spatial : Spatial)(implicit d : DummyImplicit) : String =
    spatial.map(p => pretty(p._1, p._2)).mkString(" ★ ")

  def pretty[T <: ASTType](loc : Loc, f : Fields, sep : String, e : SetExpr[T]): String =
    s"${pretty(loc)}.$f $sep ${pretty(e)}"

  def pretty(crd: Cardinality): String = crd match {
    case Single => ""
    case Many => "*"
    case Opt => "?"
  }

  def pretty(ownership: SOwnership): String = ownership match {
    case SUnowned => "-"
    case SRef => "↝"
    case SOwned(l, f) => s"◆${pretty(l)}.$f"
  }

  def pretty(ssymdesc: SSymbolDesc): String = s"(${ssymdesc.cl.name}${pretty(ssymdesc.crd)}, ${pretty(ssymdesc.ownership)})"

  def pretty(ssvltion: SetSymbolValuation)(implicit d: DummyImplicit, d2: DummyImplicit): String =
    s"[${ssvltion.map {case (ssym, ssymdesc) => s"${pretty(ssym)} ↦ ${pretty(ssymdesc)}"}.mkString(", ")}]"

  def pretty(ownership: Ownership): String = ownership match {
    case NewlyCreated => "new"
    case Unowned => "-"
    case UnknownOwner => "¿"
    case Owned(l, f) => s"◆${pretty(l)}.$f"
  }

  def pretty(symdesc: SymbolDesc): String = symdesc match {
    case Loced(l) => pretty(l)
      // TODO pretty descendant pool
    case UnknownLoc(cl, ownership, descendantpool) => s"(${cl.name}, ${pretty(ownership)}})"
  }

  def pretty(ssvltion: SymbolValuation)(implicit d: DummyImplicit, d2: DummyImplicit, d3: DummyImplicit): String =
    s"[${ssvltion.map {case (sym, symdesc) => s"${pretty(sym)} ↦ ${pretty(symdesc)}"}.mkString(", ")}]"

  def pretty(locOwnership: LocOwnership)(implicit d: DummyImplicit, d2: DummyImplicit, d3: DummyImplicit, d4:DummyImplicit): String =
    s"[${locOwnership.map {case (loc, ownership) => s"${pretty(loc)} ↦ ${pretty(ownership)}"}.mkString(", ")}]"

  def pretty(heap : SHeap): String =
    sep(sep(sep(sep(pretty(heap.ssvltion) , ";", pretty(heap.svltion)), ";", pretty(heap.locOwnership)), ";", s"${pretty(heap.currentSpatial)}"), "∧", s"(${pretty(heap.pure)})")

  def pretty(mem : SMem): String =
    sep(s"${pretty(mem.currentStack)}", ";", s"${pretty(mem.heap)}")

  def sep(s1 : String, ss : String, s2 : String) =
    if (s2.trim.isEmpty) s1
    else if (s1.trim.isEmpty) s2
    else s"$s1 $ss $s2"

  def default(s : String, sd : String) =
    if (s.trim.isEmpty) sd else s
}
