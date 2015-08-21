package syntax

package object ast {
  type Vars = String
  type Symbols = Int
  type Fields = String
  type Spatial = Map[Expr, Set[Map[SFields, Expr]]]
  type Prop = Set[SimpleProp]
  type SymbolicStack = Map[Vars, Expr]

  def not(p : SimpleProp) : SimpleProp = p match {
    case Not(p) => p
    case p => Not(p)
  } //Smart constructor
  implicit class FieldsExtra(f : Fields) {
    def field = Field(f)
  }
  def ownerinf = OwnerInfo()()
}
