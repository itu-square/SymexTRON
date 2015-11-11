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
