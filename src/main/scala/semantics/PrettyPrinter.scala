package semantics

import domains._
import syntax.ast._

object PrettyPrinter {

  def pretty(stack: SStack): String = s"[${stack.map(p => s"${p._1} ↦ ${pretty(p._2)}").mkString(", ")}]"

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
      case SetLit(es @ _*) => if (es.length <= 0) "∅" else s"{${es.map(pretty[T]).mkString(", ")}}"
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

  def pretty(sym : Symbols, spatialDesc: SpatialDesc): String = spatialDesc match {
    case SpatialDesc(c, typ, children, refs) => {
      val prettytyp = typ match {
        case ExactDesc => s"${pretty(Symbol(sym))} : ${c.name}"
        case AbstractDesc => s"inst〈${c.name}〉 ${pretty(Symbol(sym))}"
        case PartialDesc(hasExact, possible) => s"inst〈${sep(if (hasExact) s"☐${c.name}" else "", ",", possible.map(_.name).mkString(", "))}〉 ${pretty(Symbol(sym))}"
      }
      sep(prettytyp, "★",
        sep(s"${children.map(p => pretty(sym, p._1, "◆↣", p._2)).mkString(" ★ ")}", "★",
          s"${refs.map(p => pretty(sym, p._1, "↝", p._2)).mkString(" ★ ")}"))
    }
  }

  def pretty[T <: ASTType](sym : Symbols, f : Fields, sep : String, e : SetExpr[T]): String =
    s"${pretty(Symbol(sym))}.$f $sep ${pretty(e)}"

  def pretty(spatial : Spatial[Symbols])(implicit d : DummyImplicit) : String =
    spatial.map(p => pretty(p._1, p._2)).mkString(" ★ ")

  def pretty[T <: ASTType](v : Vars, f : Fields, sep : String, e : SetExpr[T]): String =
    s"$v.$f $sep ${pretty(e)}"

  def pretty(qspatial : QSpatial): String =
    s"inst⟨${qspatial.c.name}⟩ ${pretty(qspatial.e)}"

  def pretty(heap : SHeap): String =
    sep(sep(s"${pretty(heap.spatial)}", "★",
      s"${heap.qspatial.map(pretty).mkString(" ★ ")}"), "∧", s"(${pretty(heap.pure)})")

  def pretty(mem : SMem): String =
    sep(s"${pretty(mem.stack)}", ";", s"${pretty(mem.heap)}")

  def sep(s1 : String, ss : String, s2 : String) =
    if (s2.trim.isEmpty) s1
    else if (s1.trim.isEmpty) s2
    else s"$s1 $ss $s2"

  def default(s : String, sd : String) =
    if (s.trim.isEmpty) sd else s
}
