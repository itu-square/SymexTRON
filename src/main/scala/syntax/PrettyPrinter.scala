package syntax

import syntax.ast._

object PrettyPrinter {

  def pretty(stack: SStack): String = stack.map(p => s"${p._1} ↦ ${pretty(p._2)}").mkString(", ")

  def pretty(pred: Pred): String = pred match {
      case Descendant(s, e1, e2) => s"dc[$s](${pretty(e1)}, ${pretty(e2)})"
      case NotDescendant(e1, e2) => s"¬dc(${pretty(e1)}, ${pretty(e2)})"
      case Def(s, e) => s"def[$s](${pretty(e)})"
    }

  def pretty(own: OwnerInfo): String = own match {
    case Unowned() => "@owner ↝ ∅"
    case Owned(owner, f) => s"@owner[$f] ↝ ${pretty(owner)}"
  }

  def pretty(spatial: Spatial, preds: Set[Pred]): String = {
    val pmaptos = for {
      (e, fss_)  <- spatial
      fss <- fss_
      (fs, own) = fss
      sfs <- (for (fv <- fs) yield {
        s"${pretty(e)}.${fv._1} ↝ ${pretty(fv._2)}"
      }).toSet + s"${pretty(e)}${pretty(own)}"
    } yield sfs
    val ppreds = preds.map(pretty)
    (pmaptos ++ ppreds).mkString(" ★ ")
  }

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
      case Match(e, s) => s"(${pretty(e)}) match ${s.name}"
      case MatchStar(e, s) => s"(${pretty(e)}) match* ${s.name}"
    }
  }

  def pretty(sp: BoolExpr): String = sp match {
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

  def pretty(heap : SHeap): String = {
    s"${pretty(heap.spatial, heap.preds)} | ${pretty(heap.pure)}"
  }

  def pretty(mem : SMem): String =
    s"${pretty(mem.stack)} ; ${pretty(mem.heap)}"
}