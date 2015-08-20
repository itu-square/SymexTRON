package syntax.ast

import helper.{FALSE, TRUE, BOOL}

case class Sort(name: String) // To be defined later

class SortDefinition(val name: String, val children: Map[Fields, Sort], val refs: Map[Fields, Sort], supers: Sort*)

sealed trait Expr[B <: BOOL]
case class ESet() extends Expr[TRUE.V]
case class Symbol(id: Symbols) extends Expr[TRUE.V]
case class Var(name: Vars) extends Expr[FALSE.V]

sealed trait SimpleProp[B <: BOOL]

case class Eq[B1 <: BOOL, B2 <: BOOL](e1: Expr[B1], e2: Expr[B2]) extends SimpleProp[B1#AND[B2]]
case class SortMem[B <: BOOL](e1: Expr[B], s: Sort) extends SimpleProp[B]
case class Not[B <: BOOL](p: SimpleProp[B]) extends SimpleProp[B]

case class SymbolicHeap(pure : Prop, spatial : Spatial)

case class SymbolicMemory(stack: SymbolicStack, heap: SymbolicHeap)

trait Chc {
  val b: BOOL
  val e: SimpleProp[b.V]
  val c: Command
}

object Chc {
  def apply(b: BOOL)(e: SimpleProp[b.V], c: Command): Chc = {
    ChcI[b.V](b, e, c)
  }
  private case class ChcI[B <: BOOL](val b : BOOL { type V = B }, val e : SimpleProp[B], val c : Command) extends Chc
}

sealed trait Command
case class Fail() extends Command
case class CSeq(cs : Command*) extends Command
case class AssignVar[B <: BOOL](x : Vars, e : Expr[B]) extends Command
case class LoadField[B <: BOOL](x : Vars, e : Expr[B], f : Fields) extends Command
case class New(x : Vars, s : Sort) extends Command
case class AssignField[B1 <: BOOL, B2 <: BOOL](e1 : Expr[B1], f : Fields, e2 : Expr[B2]) extends Command
case class If(cs : Set[Chc]) extends Command
case class For[B <: BOOL](x : Vars, s : Sort, e : Expr[B], inv: (Symbols, Set[SymbolicMemory]), cb: Command)
  extends Command
case class ForMatch[B <: BOOL](x : Vars, s : Sort, e : Expr[B], inv: (Symbols, Set[SymbolicMemory]), cb: Command)
  extends Command
case class Fix[B <: BOOL](e : Expr[B], inv: (Symbols, Set[SymbolicMemory]), cb: Command) extends Command

sealed trait SFields
case class Field(f : Fields) extends SFields
case class OwnerInfo()(val frev : Option[Fields] = None) extends SFields
