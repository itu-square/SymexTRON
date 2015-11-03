package helper.theories

import smtlib.parser.Terms._

// Based on http://cvc4.cs.nyu.edu/wiki/Sets

object Sets {
  object SetSort {
    def apply(el : Sort): Sort = Sort(Identifier(SSymbol("Set")), Seq(el))

    def unapply(sort : Sort): Option[Sort] = sort match {
      case Sort(Identifier(SSymbol("Set"), Seq()), Seq(el)) => Some(el)
      case _ => None
    }
  }

  trait UnaryOperation {
    def name: String

    def apply(i : Term): Term =
      FunctionApplication(QualifiedIdentifier(Identifier(SSymbol(name))),
                            Seq(i))

    def unapply(t : Term): Option[Term] = t match {
      case FunctionApplication(
            QualifiedIdentifier(Identifier(SSymbol(n), Seq()), None),
            Seq(i)) if n == name => Some(i)
      case _ => None
    }
  }

  trait BinaryOperation {
    def name: String

    def apply(l : Term, r : Term): Term =
      FunctionApplication(QualifiedIdentifier(Identifier(SSymbol(name))),
                            Seq(l,r))

    def unapply(t : Term): Option[(Term, Term)] = t match {
      case FunctionApplication(
            QualifiedIdentifier(Identifier(SSymbol(n), Seq()), None),
            Seq(l,r)) if n == name => Some((l,r))
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

  object Union extends BinaryOperation { override val name = "union" }
  object Intersection extends BinaryOperation { override val name = "intersection" }
  object Setminus extends BinaryOperation { override val name = "setminus" }
  object Member extends BinaryOperation { override val name = "member" }
  object Subset extends BinaryOperation { override val name = "subset" }

  object EmptySet {
    def apply(s : Sort): Term = QualifiedIdentifier(Identifier(SSymbol("emptyset")), Some(s))
    def unapply(t : Term): Option[Sort] = t match {
      case QualifiedIdentifier(Identifier(SSymbol("emptyset"), Seq()), Some(s)) =>
          Some(s)
      case _ => None
    }
  }

  object Singleton extends UnaryOperation { override val name = "singleton" }

  object Insert extends NAryOperation { override val name = "insert" }
}
