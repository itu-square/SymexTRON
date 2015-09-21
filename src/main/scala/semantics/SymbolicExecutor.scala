package semantics

/*
Based on "Symbolic Execution with Separation Logic" by Berdine et al. (2005)
 */

import helper._
import syntax.ast._

import scalaz._, Scalaz._
import scalaz.\/.{left, right}
import SymbolicHeapChecker._
import Subst._

class SymbolicExecutor(defs: Map[Class, ClassDefinition]) {

  def execute(pres : Set[SMem], c : Statement) : String \/ Set[SMem] = {
    // Inconsistent precondition
    pres.map[String \/ Set[SMem], Set[String \/ Set[SMem]]] { pre: SMem =>
      c match {
        case Fail() => ???
        case StmtSeq(cs) => ???
        case AssignVar(x, e) => ???
        case LoadField(x, e, f) => ???
        case New(x, s) => ???
        case AssignField(e1, f, e2) => ???
        case If(cs) => ???
        case For(x, s, m, cb) => ???
        case Fix(e, inv, cb) => ???
      }
    }.foldLeft(right[String, Set[SMem]](Set())) { (acc, el) =>
      for (acc_ <- acc; el_ <- el) yield acc_ ++ el_
    }
  }

  def evalBasicExpr(s: SStack, e: BasicExpr): String \/ BasicExpr = e match {
    case Symbol(id) => right(Symbol(id))
    case Var(name) =>
      s.get(name).fold[String \/ BasicExpr](left(s"Error while evaluating expression $e"))((ee : SetExpr) =>
        ee match {
          case SetLit(evalue) => right(evalue)
          case _ => left(s"Not a basic expression: $ee")
        })
  }

  def evalExpr(s : SStack, e : SetExpr) : String \/ SetExpr = {
      type StringE[B] = String \/ B
      e match {
        case SetLit(es @ _*) =>
          for {
            ees <- es.toList.traverse[StringE, BasicExpr](e => evalBasicExpr(s, e))
          } yield SetLit(ees : _*)
        case SetSymbol(ident) => right(SetSymbol(ident))
        case SetVar(name) =>
          // Scalas type inference is really primitive...
          s.get(name).fold[String \/ SetExpr](left(s"Error while evaluating expression $e"))(right)
        case Diff(e1, e2) => for {
          ee1 <- evalExpr(s, e1)
          ee2 <- evalExpr(s, e2)
        } yield Diff(e1, e2)
        case Union(e1, e2) => for {
          ee1 <- evalExpr(s, e1)
          ee2 <- evalExpr(s, e2)
        } yield Union(e1, e2)
        case ISect(e1, e2) => for {
          ee1 <- evalExpr(s, e1)
          ee2 <- evalExpr(s, e2)
        } yield ISect(e1, e2)
        case GuardedSet(e1, guard) => for {
          ee1 <- evalExpr(s, e1)
          eguard <- evalSimpleProp(s, guard)
        } yield GuardedSet(ee1, eguard)
      }
    }
  
  def evalBoolExpr(st : SStack, sp : BoolExpr) : String \/ BoolExpr = sp match {
    case Eq(e1, e2) =>
      for {
        ee1 <- evalExpr(st, e1)
        ee2 <- evalExpr(st, e2)
      } yield Eq(ee1, ee2)
    case ClassMem(e1, s) =>
      for {
        ee1 <- evalExpr(st, e1)
      } yield ClassMem(ee1, s)
    case Not(p) =>
      for {
        ep <- evalBoolExpr(st, p)
      } yield Not(ep)
    case SetMem(e1, e2) =>
      for {
        ee1 <- evalBasicExpr(st, e1)
        ee2 <- evalExpr(st, e2)
      } yield SetMem(ee1, ee2)
    case SetSub(e1, e2) =>
      for {
        ee1 <- evalExpr(st, e1)
        ee2 <- evalExpr(st, e2)
      } yield SetSub(ee1, ee2)
    case SetSubEq(e1, e2) =>
      for {
        ee1 <- evalExpr(st, e1)
        ee2 <- evalExpr(st, e2)
      } yield SetSubEq(ee1, ee2)
  }

  private var symCounter = Ref(0)

  private def freshSym(): Symbols = {
    val old = !symCounter
    symCounter := !symCounter + 1
    old
  }
}
