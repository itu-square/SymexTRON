package syntax.ast

import helper.{FALSE, TRUE, BOOL}

case class Sort(name: String) // To be defined later

class SortDefinition(val name: String, val children: Map[Fields, Sort], val fields: Map[Fields, Sort])


sealed trait Expr[B <: BOOL]
case class Nil() extends Expr[TRUE.V]
case class Symbol(id: Symbols) extends Expr[TRUE.V]
case class Var(name: Vars) extends Expr[FALSE.V]

sealed trait SimpleProp[B <: BOOL]

case class Eq[B1 <: BOOL, B2 <: BOOL](e1: Expr[B1], e2: Expr[B2]) extends SimpleProp[B1#AND[B2]]
case class SortMem[B <: BOOL](e1: Expr[B], s: Sort) extends SimpleProp[B]
case class Not[B <: BOOL](p: SimpleProp[B]) extends SimpleProp[B]

case class SymbolicHeap(pure : Prop, spatial : Spatial)

case class SymbolicMemory(stack: SymbolicStack, heap: SymbolicHeap)

sealed trait Command
case class Skip() extends Command
case class Fail() extends Command
case class Seq(cs : Command*) extends Command
case class AssignVar(x : Vars, e : Expr[FALSE.V]) extends Command
case class Load(x : Vars, e : Expr[FALSE.V], f : Fields) extends Command
case class New(x : Vars, s : Sort) extends Command
case class AssignField(e1 : Expr[FALSE.V], f : Fields, e2 : Expr[FALSE.V]) extends Command
case class If(cs : Set[(SimpleProp[FALSE.V], Command)]) extends Command
case class For(x : Vars, s : Sort, e : Expr[FALSE.V], inv: (Symbols, Set[SymbolicMemory]), cb: Command)
  extends Command
case class ForMatch(x : Vars, s : Sort, e : Expr[FALSE.V], inv: (Symbols, Set[SymbolicMemory]), cb: Command)
  extends Command
case class Fix(e : Expr[FALSE.V], inv: (Symbols, Set[SymbolicMemory]), cb: Command) extends Command
