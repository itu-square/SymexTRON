package semantics

/*
Based on "Symbolic Execution with Separation Logic" by Berdine et al. (2005)
 */

import _root_.syntax.PrettyPrinter
import helper._
import syntax.ast._

import scalaz._, Scalaz._
import scalaz.\/.{left, right}
import Subst._

class SymbolicExecutor(defs: Map[Class, ClassDefinition]) {
  private type StringE[B] = String \/ B

  def access(e: SetExpr, f: Fields, heap: SHeap): String \/ SetExpr = ???

  def update(sym: Symbols, f: Fields, ee2: SetExpr, heap: SHeap): String \/ SHeap = ???

  def execute(pres : Set[SMem], c : Statement) : String \/ Set[SMem] = {
    // Inconsistent precondition
    pres.map[String \/ Set[SMem], Set[String \/ Set[SMem]]] { pre: SMem =>
      c match {
        case StmtSeq(ss@_*) => ss.toList.foldLeftM[StringE, Set[SMem]](Set(pre))(execute)
        case AssignVar(x, e) => for {
          ee <- evalExpr(pre.stack, e)
        } yield Set(SMem(pre.stack + (x -> ee), pre.heap))
        case New(x, c) => for {
          cdef <- defs.get(c).cata(right, left(s"Unknown class: $c"))
          xsym = freshSym
          newspatial =
              xsym -> ConcreteDesc(c, cdef.children.mapValues(_ => SetLit()), cdef.refs.mapValues(_ => SetLit()))
        } yield Set(SMem(pre.stack + (x -> SetLit(Symbol(xsym))),
                    SHeap(pre.heap.spatial + newspatial, pre.heap.qspatial, pre.heap.pure)))
        case LoadField(x, e, f) => for {
          ee <- evalExpr(pre.stack, e)
          er <- access(ee, f, pre.heap)
        } yield Set(SMem(pre.stack + (x -> er), pre.heap))
        case AssignField(e1, f, e2) => for {
          sym <- evalExpr(pre.stack, e1).flatMap(getSymbol)
          ee2 <- evalExpr(pre.stack, e2)
          newheap <- update(sym, f, ee2, pre.heap)
        } yield Set(SMem(pre.stack, newheap))
        case If(cs@_*) => {
          val ecs = cs.map(p => (evalBoolExpr(pre.stack, p._1), p._2))
          (for {
            cstmt <- ecs
            (eb, s) = cstmt
            posts = (for {
              eeb <- eb
              res <- execute(Set(SMem(pre.stack, SHeap(pre.heap.spatial, pre.heap.qspatial, pre.heap.pure + eeb))), s)
            } yield res)
          } yield posts).toList.sequence[StringE, Set[SMem]].map(_.toSet.flatten)
          }
        case For(x, c, m, sb) => ???
        case Fix(e, sb) => ???
      }
    }.foldLeft(right[String, Set[SMem]](Set())) { (acc, el) =>
      for (acc_ <- acc; el_ <- el) yield acc_ ++ el_
    }
  }

  def getSymbol(e : SetExpr): String \/ Symbols = {
    e match {
      case SetLit(Symbol(sym)) => right(sym)
      case _ => left(s"${PrettyPrinter.pretty(e)} is not a symbol")
    }
  }

  def evalBasicExpr(s: SStack, e: BasicExpr): String \/ BasicExpr = e match {
    case Symbol(id) => right(Symbol(id))
    case Var(name) =>
      s.get(name).fold[String \/ BasicExpr](left(s"Error while evaluating expression $e")) {
        (ee: SetExpr) =>
          ee match {
            case SetLit(evalue) => right(evalue)
            case _ => left(s"Not a basic expression: $ee")
          }
      }
  }

  def evalExpr(s : SStack, e : SetExpr) : String \/ SetExpr = {
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
          eguard <- evalBoolExpr(s, guard)
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

  private def freshSym: Symbols = {
    val old = !symCounter
    symCounter := !symCounter + 1
    old
  }

  private val childfields: Set[Fields] = defs.values.flatMap(_.children.map(_._1)).toSet
  private val reffields: Set[Fields]   = defs.values.flatMap(_.refs.map(_._1)).toSet

  {
    val commoncr = childfields intersect reffields
    assert(commoncr.isEmpty, s"There are overlapping names used for fields and references: ${commoncr.mkString(", ")}")
  }
}
