package semantics

import org.kiama.rewriting.Rewriter._
import org.kiama.rewriting.Strategy
import syntax.ast._

object SetNormalizer {
  //Use non-deterministic definitions
  // TODO: Improve membership resolution
  def normalize(props : Prop) : Strategy = repeat("normalize", rule[SetExpr] {
    case Union(e1, e2) if e1 == e2 => e1
  } + rule[SetExpr] {
    case ISect(e1, e2) if e1 == e2 => e1
  } + rule[SetExpr] {
    case Diff(e1, e2) if e1 == e2 => SetLit()
  } + rule[SetExpr] {
    case Union(e, SetLit()) => e
    case Union(SetLit(), e) => e
  } + rule[SetExpr] {
    case ISect(e, SetLit()) => SetLit()
    case ISect(SetLit(), e) => SetLit()
  } + rule[SetExpr] {
    case Diff(e, SetLit()) => e
  } + rule[SetExpr] {
    case Diff(SetLit(), e) => SetLit()
  } + rule[SetExpr] {
    case Union(e, SetLit(a)) if props.contains(SetMem(a, e)) => e
    case Union(SetLit(a), e) if props.contains(SetMem(a, e)) => e
  } + rule[SetExpr] {
    case ISect(e, SetLit(a)) if props.contains(SetMem(a, e)) => SetLit(a)
    case ISect(SetLit(a), e) if props.contains(SetMem(a, e)) => SetLit(a)
  } + rule[SetExpr] {
    case ISect(e, SetLit(a)) if props.contains(Not(SetMem(a, e))) => SetLit()
    case ISect(SetLit(a), e) if props.contains(Not(SetMem(a, e))) => SetLit()
  } + rule[SetExpr] {
    case Diff(e, SetLit(a)) if props.contains(Not(SetMem(a, e))) => e
  } + strategy[SetExpr] {
    case Union(e1, e2) => {
      val a = props.map(p => p match {
        case SetMem(a, e1_) if e1 == e1_  && props.contains(SetMem(a, e2))
             => Some(SetLit(a))
        case _ => None
      }).filter(_.isDefined).headOption.flatten
      a match {
        case Some(a) => Some(Union(e1, Diff(e2, a)))
        case None => None
      }
    }
  } + rule[SetExpr] {
    case SetLit(a1, a2, as @ _*) => Union(SetLit(a1), SetLit((a2 +: as) : _*))
  } + rule[SetExpr] {
    case ISect(Union(e1, e2), e3) => Union(ISect(e1, e3), ISect(e2, e3))
    case ISect(e1, Union(e2, e3)) => Union(ISect(e1, e2), ISect(e1, e3))
  } + rule[SetExpr] {
    case Diff(Union(e1,e2), e3) => Union(Diff(e1, e3), Diff(e2, e3))
  })
}
