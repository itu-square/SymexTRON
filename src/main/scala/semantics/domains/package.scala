package semantics

import syntax.ast._

import scalaz._, Scalaz._

/**
  * Created by asal on 19/01/2016.
  */
package object domains extends SymbolicOps {
  type Spatial = Map[Symbols, SpatialDesc]
  type Prop = Set[BoolExpr[IsSymbolic.type]]
  type SStack = Map[Vars, SetExpr[IsSymbolic.type]]
  type Instances = Int
  type CStack = Map[Vars, Set[Instances]]


  def getSingletonSymbolId(e : SetExpr[IsSymbolic.type]): String \/ Symbols = {
    e match {
      case SetLit(Symbol(sym)) => sym.right
      case _ => s"${PrettyPrinter.pretty(e)} is not a single symbol".left
    }
  }
}
