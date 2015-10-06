package syntax

package object ast {
  type Vars = String
  type Symbols = Int
  type Fields = String
  type Spatial[T] = Map[T, SpatialDesc]
  type Prop = Set[BoolExpr]
  type SStack = Map[Vars, SetExpr]

  def not(p : BoolExpr) : BoolExpr = p match {
    case Not(p) => p
    case p => Not(p)
  } //Smart constructor
}
