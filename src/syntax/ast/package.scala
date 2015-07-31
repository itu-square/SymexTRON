package syntax

import helper.MultiMap

package object ast {
  type Vars = String
  type Fields = String
  type Spatial = Map[Expr, Set[Map[Fields, Expr]]]
  type Prop = Set[SimpleProp]

  def not(p : SimpleProp) : SimpleProp = p match {
    case Not(e) => e
    case Eq(e1, e2) => Not(Eq(e1, e2))
  } //Smart constructor
}
