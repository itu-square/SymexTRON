package syntax

import helper.{BOOL, TRUE}

package object ast {
  type Vars = String
  type Symbols = Int
  type Fields = String
  type Spatial = Map[Expr[TRUE.V], Set[Map[Fields, Expr[TRUE.V]]]]
  type Prop = Set[SimpleProp[TRUE.V]]
  type SymbolicStack = Map[Vars, Expr[TRUE.V]]

  def not[B <: BOOL](p : SimpleProp[B]) : SimpleProp[B] = p match {
    case NotEq(e1, e2) => Eq(e1, e2)
    case Eq(e1, e2) => NotEq(e1, e2)
    case SortMem(e, s) => NotSortMem(e, s)
    case NotSortMem(e, s) => SortMem(e, s)
  } //Smart constructor
}
