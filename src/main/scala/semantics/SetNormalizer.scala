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
    case Diff(e1, e2) if e1 == e2 => SetE()
  } + rule[SetExpr] {
    case Union(e, SetE()) => e
    case Union(SetE(), e) => e
  } + rule[SetExpr] {
    case ISect(e, SetE()) => SetE()
    case ISect(SetE(), e) => SetE()
  } + rule[SetExpr] {
    case Diff(e, SetE()) => e
  } + rule[SetExpr] {
    case Diff(SetE(), e) => SetE()
  } + rule[SetExpr] {
    case Union(e, SetE(a)) if props.contains(SetMem(a, e)) => e
    case Union(SetE(a), e) if props.contains(SetMem(a, e)) => e
  } + rule[SetExpr] {
    case ISect(e, SetE(a)) if props.contains(SetMem(a, e)) => SetE(a)
    case ISect(SetE(a), e) if props.contains(SetMem(a, e)) => SetE(a)
  } + rule[SetExpr] {
    case ISect(e, SetE(a)) if props.contains(Not(SetMem(a, e))) => SetE()
    case ISect(SetE(a), e) if props.contains(Not(SetMem(a, e))) => SetE()
  } + rule[SetExpr] {
    case Diff(e, SetE(a)) if props.contains(Not(SetMem(a, e))) => e
  } + strategy[SetExpr] {
    case Union(e1, e2) => {
      val a = props.map(p => p match {
        case SetMem(a, e1_) if e1 == e1_  && props.contains(SetMem(a, e2))
             => Some(SetE(a))
        case _ => None
      }).filter(_.isDefined).headOption.flatten
      a match {
        case Some(a) => Some(Union(e1, Diff(e2, a)))
        case None => None
      }
    }
  } + rule[SetExpr] {
    case SetE(a1, a2, as @ _*) => Union(SetE(a1), SetE((a2 +: as) : _*))
  } + rule[SetExpr] {
    case ISect(Union(e1, e2), e3) => Union(ISect(e1, e3), ISect(e2, e3))
    case ISect(e1, Union(e2, e3)) => Union(ISect(e1, e2), ISect(e1, e3))
  } + rule[SetExpr] {
    case Diff(Union(e1,e2), e3) => Union(Diff(e1, e3), Diff(e2, e3))
  })
}
