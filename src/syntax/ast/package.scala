package syntax

import helper.{BOOL, TRUE}

package object ast {
  type Vars = String
  type Symbols = Int
  type Fields = String
  type Spatial = Map[Expr[TRUE.V], Set[Map[SFields, Expr[TRUE.V]]]]
  type Prop = Set[SimpleProp[TRUE.V]]
  type SymbolicStack = Map[Vars, Expr[TRUE.V]]

  def not[B <: BOOL](p : SimpleProp[B]) : SimpleProp[B] = p match {
    case Not(p) => p
    case p => Not(p)
  } //Smart constructor
  implicit class FieldsExtra(f : Fields) {
    def fi = Field(f)
  }
  def ownerinf = OwnerInfo()()
}
