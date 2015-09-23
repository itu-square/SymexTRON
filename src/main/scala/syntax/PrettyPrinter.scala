package syntax

import syntax.ast._

object PrettyPrinter {

  def pretty(stack: SStack): String = s"[${stack.map(p => s"${p._1} ↦ ${pretty(p._2)}").mkString(", ")}]"

  private val symbs = "αβγδεζηθικλμνξοxπρςστυφχψω"

  def pretty(e : BasicExpr): String = {
    e match {
      case Symbol(ident) =>
        val l = symbs.length
        val i = ident / l
        s"${symbs(ident % l)}${if (i <= 0) "" else s"'$i"}"
      case Var(name) => name
    }
  }

  def pretty(e : SetExpr): String = {
    e match {
      case SetSymbol(ident) =>
        val l = symbs.length
        val i = ident / l
        s"${symbs(ident % l).toTitleCase}${if (i <= 0) "" else s"'$i"}"
      case SetVar(name) => name
      case SetLit(es @ _*) => if (es.length <= 0) "∅" else s"{${es.map(pretty).mkString(", ")}}"
      case Union(e1, e2) => s"${pretty(e1)} ∪ ${pretty(e2)}"
      case Diff(e1, e2) => s"${pretty(e1)} ∖ ${pretty(e2)}"
      case ISect(e1, e2) => s"${pretty(e1)} ∩ ${pretty(e2)}"
      case GuardedSet(e1, guard) => s"[${pretty(e1)}]⟨${pretty(guard)}⟩"
    }
  }

  def pretty(sp: BoolExpr): String = sp match {
    case Eq(e1, e2) => s"${pretty(e1)} = ${pretty(e2)}"
    case ClassMem(e1, s) => s"${pretty(e1)} : ${s.name}"
    case SetMem(e1, e2) => s"${pretty(e1)} ∈ ${pretty(e2)}"
    case SetSub(e1, e2) => s"${pretty(e1)} ⊂ ${pretty(e2)}"
    case SetSubEq(e1, e2) => s"${pretty(e1)} ⊆ ${pretty(e2)}"
    case And() => "true"
    case And(e, es@_*) => es.foldLeft(pretty(e)) { (s1 : String, b : BoolExpr) => sep(s1, "∧", pretty(b)) }
    case Not(p) => p match {
      case Eq(e1, e2) => s"${pretty(e1)} ≠ ${pretty(e2)}"
      case ClassMem(e1, s) => s"¬(${pretty(e1)} : ${s.name})"
      case SetMem(e1, e2) => s"${pretty(e1)} ∉ ${pretty(e2)}"
      case SetSub(e1, e2) => s"${pretty(e1)} ⊄ ${pretty(e2)}"
      case SetSubEq(e1, e2) => s"${pretty(e1)} ⊈ ${pretty(e2)}"
      case And() => "false"
      case And(e, es@_*) if (e +: es) forall (_.isInstanceOf[Not])
         => es.foldLeft(pretty(e)) { (s1 : String, b : BoolExpr) => sep(s1, "∨", pretty(b)) }
      case And(e, es@_*) => s"¬(${es.foldLeft(pretty(e)) { (s1 : String, b : BoolExpr) => sep(s1, "∧", pretty(b)) }})"
      case Not(p) => s"${pretty(p)}"
    }
  }

  def pretty(pure: Prop): String = pure.map(pretty).mkString(" ∧ ")

  def pretty(sym : Symbols, spatialDesc: SpatialDesc): String = spatialDesc match {
    case AbstractDesc(c, unowned) => s"${pretty(Symbol(sym))} <: $c ⟨${pretty(unowned)}⟩"
    case ConcreteDesc(c, children, refs) => sep(s"${pretty(Symbol(sym))} : $c", "★",
                                            sep(s"${children.map(p => pretty(sym, p._1, "◆↣", p._2)).mkString(" ★ ")}", "★",
                                                s"${refs.map(p => pretty(sym, p._1, "↝", p._2)).mkString(" ★ ")}"))
  }

  def pretty(sym : Symbols, f : Fields, sep : String, e : SetExpr): String =
    s"${pretty(Symbol(sym))}.$f $sep ${pretty(e)}"

  def pretty(spatial : Spatial[Symbols])(implicit d : DummyImplicit) : String =
    spatial.map(p => pretty(p._1, p._2)).mkString(" ★ ")

  //TODO Avoid code duplication between vars and symbols

  def pretty(v : Vars, spatialDesc: SpatialDesc): String = spatialDesc match {
    case AbstractDesc(c, unowned) => s"$v <: $c ⟨${pretty(unowned)}⟩"
    case ConcreteDesc(c, children, refs) => sep(s"$v : $c", "★",
      sep(s"${children.map(p => pretty(v, p._1, "◆↣", p._2)).mkString(" ★ ")}", "★",
        s"${refs.map(p => pretty(v, p._1, "↝", p._2)).mkString(" ★ ")}"))
  }

  def pretty(v : Vars, f : Fields, sep : String, e : SetExpr): String =
    s"$v.$f $sep ${pretty(e)}"

  def pretty(spatial : Spatial[Vars])(implicit d : DummyImplicit, d2 : DummyImplicit) : String =
    spatial.map(p => pretty(p._1, p._2)).mkString(" ★ ")

  def pretty(qspatial : QSpatial): String =
    s"✪⟨${qspatial._1} ∈ ${pretty(qspatial._2)}⟩ ${pretty(qspatial._3)}"

  def pretty(heap : SHeap): String =
    sep(s"${pretty(heap.spatial)}", "★",
      sep(s"${heap.qspatial.map(pretty).mkString(" ★ ")}}", "∧", s"(${pretty(heap.pure)})"))

  def pretty(mem : SMem): String =
    sep(s"${pretty(mem.stack)}", ";", s"${pretty(mem.heap)}")

  def sep(s1 : String, ss : String, s2 : String) =
    if (s2.trim.isEmpty) s1
    else if (s1.trim.isEmpty) s2
    else s"$s1 $ss $s2"

  def default(s : String, sd : String) =
    if (s.trim.isEmpty) sd else s
}