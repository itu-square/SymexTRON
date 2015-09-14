package syntax

package object ast {
  type Vars = String
  type Symbols = Int
  type Fields = String
  type Spatial = Map[SetExpr, Set[(Map[Fields, SetExpr], OwnerInfo)]]
  type Prop = Set[BoolExpr]
  type SymbolicStack = Map[Vars, SetExpr]

  def not(p : BoolExpr) : BoolExpr = p match {
    case Not(p) => p
    case p => Not(p)
  } //Smart constructor
}
