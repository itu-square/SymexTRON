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

  def seq(c1: Command, c2: Command): Command = c1 match {
    case Skip() => c2
    case Fail() => Fail()
    case AssignVar(x, e, c) => AssignVar(x, e, seq(c, c2))
    case Load(x, e, f, c) => Load(x, e, f, seq(c, c2))
    case New(x, s, c) => New(x, s, seq(c, c2))
    case AssignField(e1, f, e2, c) => AssignField(e1, f, e2, seq(c, c2))
    case If(cs, c) => If(cs, seq(c, c2))
    case For(x, s, e, inv, cb, c) => For(x, s, e, inv, cb, seq(c, c2))
    case ForMatch(x, s, e, inv, cb, c) => ForMatch(x, s, e, inv, cb, seq(c, c2))
  }
}
