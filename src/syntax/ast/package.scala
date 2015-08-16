package syntax

package object ast {
  type Vars = String
  type Symbols = Int
  type Fields = String
  type Spatial = Map[Expr, Set[Map[Fields, Expr]]]
  type Prop = Set[SimpleProp]
  type Stacks = Map[Vars, Symbols]

  def not(p : SimpleProp) : SimpleProp = p match {
    case NotEq(e1, e2) => Eq(e1, e2)
    case Eq(e1, e2) => NotEq(e1, e2)
  } //Smart constructor
}
