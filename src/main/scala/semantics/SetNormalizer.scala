package semantics

import org.kiama.rewriting.Rewriter._
import org.kiama.rewriting.Strategy
import syntax.ast._

object SetNormalizer {
  //Use non-deterministic definitions
  // TODO: Improve membership resolution
  def normalize(props : Prop) : Strategy = repeat("normalize", rule[Expr] {
    case Union(e1, e2) if e1 == e2 => e1
  } + rule[Expr] {
    case ISect(e1, e2) if e1 == e2 => e1
  } + rule[Expr] {
    case Diff(e1, e2) if e1 == e2 => SetE()
  } + rule[Expr] {
    case Union(e, SetE()) => e
    case Union(SetE(), e) => e
  } + rule[Expr] {
    case ISect(e, SetE()) => SetE()
    case ISect(SetE(), e) => SetE()
  } + rule[Expr] {
    case Diff(e, SetE()) => e
  } + rule[Expr] {
    case Diff(SetE(), e) => SetE()
  } + rule[Expr] {
    case Union(e, SetE(a)) if props.contains(SetMem(a, e)) => e
    case Union(SetE(a), e) if props.contains(SetMem(a, e)) => e
  } + rule[Expr] {
    case ISect(e, SetE(a)) if props.contains(SetMem(a, e)) => SetE(a)
    case ISect(SetE(a), e) if props.contains(SetMem(a, e)) => SetE(a)
  } + rule[Expr] {
    case ISect(e, SetE(a)) if props.contains(Not(SetMem(a, e))) => SetE()
    case ISect(SetE(a), e) if props.contains(Not(SetMem(a, e))) => SetE()
  } + rule[Expr] {
    case Diff(e, SetE(a)) if props.contains(Not(SetMem(a, e))) => e
  } + strategy[Expr] {
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
  } + rule[Expr] {
    case SetE(a, as @ _*) => Union(a, SetE(as : _*))
  } + rule[Expr] {
    case ISect(Union(e1, e2), e3) => Union(ISect(e1, e3), ISect(e2, e3))
    case ISect(e1, Union(e2, e3)) => Union(ISect(e1, e2), ISect(e1, e3))
  } + rule[Expr] {
    case Diff(Union(e1,e2), e3) => Union(Diff(e1, e3), Diff(e2, e3))
  })
}
