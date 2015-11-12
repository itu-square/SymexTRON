package helper.theories

import smtlib.parser.Terms._

trait UnaryOperation {
  val name: String

  def apply(i : Term): Term =
    FunctionApplication(QualifiedIdentifier(Identifier(SSymbol(name))),
                          Seq(i))

  def unapply(t : Term): Option[Term] = t match {
    case FunctionApplication(
          QualifiedIdentifier(Identifier(SSymbol(`name`), Seq()), None),
          Seq(i)) => Some(i)
    case _ => None
  }
}

trait BinaryOperation {
  val name: String

  def apply(l : Term, r : Term): Term =
    FunctionApplication(QualifiedIdentifier(Identifier(SSymbol(name))),
                          Seq(l,r))

  def unapply(t : Term): Option[(Term, Term)] = t match {
    case FunctionApplication(
          QualifiedIdentifier(Identifier(SSymbol(`name`), Seq()), None),
          Seq(l,r)) => Some((l,r))
    case _ => None
  }
}

trait TernaryOperation {
  val name: String

  def apply(t1 : Term, t2 : Term, t3: Term): Term =
    FunctionApplication(QualifiedIdentifier(Identifier(SSymbol(name))),
                          Seq(t1,t2,t3))

  def unapply(t : Term): Option[(Term, Term, Term)] = t match {
    case FunctionApplication(
          QualifiedIdentifier(Identifier(SSymbol(`name`), Seq()), None),
          Seq(t1,t2,t3)) => Some((t1,t2,t3))
    case _ => None
  }
}

trait NAryOperation {
  def name: String

  def apply(is: Seq[Term]): Term =
    FunctionApplication(QualifiedIdentifier(Identifier(SSymbol(name))), is)

  def unapply(t : Term): Option[Seq[Term]] = t match {
    case FunctionApplication(
          QualifiedIdentifier(Identifier(SSymbol(n), Seq()), None),
          is) if n == name => Some(is)
    case _ => None
  }
}
