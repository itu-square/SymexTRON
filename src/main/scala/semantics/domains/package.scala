package semantics

import syntax.ast._

import scalaz._, Scalaz._

/**
  * Created by asal on 19/01/2016.
  */
package object domains extends SymbolicOps {
  type SymbolValuation = Map[Symbol, SymbolDesc]
  type SetSymbolValuation = Map[SetSymbol, SSymbolDesc]
  type LocOwnership = Map[Loc, Ownership]
  type Spatial = Map[Loc, SpatialDesc]
  type Prop = Set[BoolExpr[IsSymbolic.type]]
  type SStack = Map[Vars, SetExpr[IsSymbolic.type]]
  type DescendantPool = Map[Class, SetExpr[IsSymbolic.type]]
  type Instances = Int
  type CStack = Map[Vars, Set[Instances]]


  def getSingletonSymbol(e : SetExpr[IsSymbolic.type]): String \/ Symbol = {
    e match {
      case SetLit(Seq(sym@Symbol(symid))) => sym.right
      case _ => s"${PrettyPrinter.pretty(e)} is not a single symbol".left
    }
  }
}
