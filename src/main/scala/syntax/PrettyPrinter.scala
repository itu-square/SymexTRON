package syntax

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
    s"${symbs(j)}${if (ident >= 0) (if (i == 0) "" else s"`$i") else "´"}"
  }

  def pretty(e : BasicExpr): String = {
    e match {
      case Symbol(ident) => prettySymb(ident)
      case Var(name) => name
    }
  }

  def pretty(e : SetExpr): String = {
    e match {
      case SetSymbol(c,ident) => s"${prettySymb(ident).toUpperCase} ⟨${c.name}⟩"
      case SetVar(name) => name
      case SetLit(es @ _*) => if (es.length <= 0) "∅" else s"{${es.map(pretty).mkString(", ")}}"
      case Union(e1, e2) => s"(${pretty(e1)} ∪ ${pretty(e2)})"
      case Diff(e1, e2) => s"(${pretty(e1)} ∖ ${pretty(e2)})"
      case ISect(e1, e2) => s"(${pretty(e1)} ∩ ${pretty(e2)})"
    }
  }

  def pretty(sp: BoolExpr): String = sp match {
    case Eq(e1, e2) => s"(${pretty(e1)} = ${pretty(e2)})"
    case ClassMem(e1, s) => s"(${pretty(e1)} : ${s.name})"
    case SetMem(e1, e2) => s"(${pretty(e1)} ∈ ${pretty(e2)})"
    case SetSubEq(e1, e2) => s"(${pretty(e1)} ⊆ ${pretty(e2)})"
    case True() => "true"
    case And(e1, e2) => s"(${pretty(e1)} ∧ ${pretty(e2)})"
    case Not(p) => p match {
      case Eq(e1, e2) => s"(${pretty(e1)} ≠ ${pretty(e2)})"
      case ClassMem(e1, s) => s"¬(${pretty(e1)} : ${s.name})"
      case SetMem(e1, e2) => s"(${pretty(e1)} ∉ ${pretty(e2)})"
      case SetSubEq(e1, e2) => s"(${pretty(e1)} ⊈ ${pretty(e2)})"
      case True() => "false"
      case And(e1 : Not, e2 : Not)
         => s"(${pretty(e1)} ∨ ${pretty(e2)})"
      case And(e1, e2) => s"¬(${pretty(e1)} ∧ ${pretty(e2)})"
      case Not(p) => s"${pretty(p)}"
    }
  }

  def pretty(pure: Prop): String = pure.map(pretty).mkString(" ∧ ")

  def pretty(sym : Symbols, spatialDesc: SpatialDesc): String = spatialDesc match {
    case AbstractDesc(c) => s"inst⟨${c.name}⟩ ${pretty(Symbol(sym))}"
    case ConcreteDesc(c, children, refs) => sep(s"${pretty(Symbol(sym))} : ${c.name}", "★",
                                            sep(s"${children.map(p => pretty(sym, p._1, "◆↣", p._2)).mkString(" ★ ")}", "★",
                                                s"${refs.map(p => pretty(sym, p._1, "↝", p._2)).mkString(" ★ ")}"))
  }

  def pretty(sym : Symbols, f : Fields, sep : String, e : SetExpr): String =
    s"${pretty(Symbol(sym))}.$f $sep ${pretty(e)}"

  def pretty(spatial : Spatial[Symbols])(implicit d : DummyImplicit) : String =
    spatial.map(p => pretty(p._1, p._2)).mkString(" ★ ")

  def pretty(v : Vars, f : Fields, sep : String, e : SetExpr): String =
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
