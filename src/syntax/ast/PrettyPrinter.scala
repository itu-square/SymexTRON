package syntax

import syntax.ast._

object PrettyPrinter {

  def pretty(stack: SymbolicStack): String = stack.map(p => s"${p._1} ↦ ${pretty(p._2)}").mkString(", ")

  def pretty(pred: Pred): String = pred match {
      case Descendant(s, e1, e2) => s"dc[$s](${pretty(e1)}, ${pretty(e2)})"
      case NotDescendant(e1, e2) => s"¬dc(${pretty(e1)}, ${pretty(e2)})"
      case Def(s, e) => s"def[$s](${pretty(e)})"
    }

  def pretty(f: SFields) = f match {
    case Field(f) => s".$f"
    case o@OwnerInfo() => o.frev.fold("@owner")(frev => s"@owner[$frev]")
  }

  def pretty(spatial: Spatial, preds: Set[Pred]): String = {
    val pmaptos = for {
      (e, fss)  <- spatial
      fs <- fss
      (f, v) <- fs
    } yield s"${pretty(e)}${pretty(f)} ↝ ${pretty(v)}"
    val ppreds = preds.map(pretty)
    (pmaptos ++ ppreds).mkString(" ★ ")
  }

  def pretty(e : Expr): String = {
    val symbs = "αβγδεζηθικλμνξοxπρςστυφχψω"
    e match {
      case Symbol(ident) =>
        val l = symbs.length
        val i = ident / l
        s"${symbs(ident % l)}${if (i <= 0) "" else s"'$i"}"
      case Var(name) => name
      case SetE(es @ _*) => if (es.length <= 0) "∅" else s"{${es.map(pretty).mkString(", ")}}"
      case Union(e1, e2) => s"${pretty(e1)} ∪ ${pretty(e2)}"
      case Diff(e1, e2) => s"${pretty(e1)} ∖ ${pretty(e2)}"
      case ISect(e1, e2) => s"${pretty(e1)} ∩ ${pretty(e2)}"
    }
  }

  def pretty(sp: SimpleProp): String = sp match {
    case Eq(e1, e2) => s"${pretty(e1)} = ${pretty(e2)}"
    case SortMem(e1, s) => s"${pretty(e1)} :∈ ${s.name}"
    case SetMem(e1, e2) => s"${pretty(e1)} ∈ ${pretty(e2)}"
    case SetSub(e1, e2) => s"${pretty(e1)} ⊂ ${pretty(e2)}"
    case SetSubEq(e1, e2) => s"${pretty(e1)} ⊆ ${pretty(e2)}"
    case Not(p) => p match {
      case Eq(e1, e2) => s"${pretty(e1)} ≠ ${pretty(e2)}"
      case SortMem(e1, s) => s"${pretty(e1)} :∉ ${s.name}"
      case SetMem(e1, e2) => s"${pretty(e1)} ∉ ${pretty(e2)}"
      case SetSub(e1, e2) => s"${pretty(e1)} ⊄ ${pretty(e2)}"
      case SetSubEq(e1, e2) => s"${pretty(e1)} ⊈ ${pretty(e2)}"
      case Not(p) => s"${pretty(p)}"
    }
  }

  def pretty(pure: Prop): String = pure.map(pretty).mkString(" ∧ ")

  def pretty(mem : SymbolicMemory): String =
    s"${pretty(mem.stack)} ; ${pretty(mem.heap.spatial, mem.heap.preds)} | ${pretty(mem.heap.pure)}"
}