package syntax

package object ast {
  type Vars = String
  type Symbols = Int
  type Fields = String
  type Spatial = Map[Expr, Set[(Map[Fields, Expr], OwnerInfo)]]
  type Prop = Set[SimpleProp]
  type SymbolicStack = Map[Vars, Expr]

  def not(p : SimpleProp) : SimpleProp = p match {
    case Not(p) => p
    case p => Not(p)
  } //Smart constructor
}
