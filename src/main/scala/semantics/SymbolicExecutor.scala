package semantics

/*
Based on "Symbolic Execution with Separation Logic" by Berdine et al. (2005)
 */

import _root_.syntax.{ast, PrettyPrinter}
import helper._
import syntax.ast._

import scalaz._, Scalaz._
import scalaz.\/.{left, right}
import Subst._

class SymbolicExecutor(defs: Map[Class, ClassDefinition],
                       nabla: (Prop, BoolExpr) => Prop = _ + _, delta: Int = 3, beta: Int = 5) {
  private type StringE[B] = String \/ B

  def access(e: SetExpr, f: Fields, heap: SHeap): String \/ SetExpr = ???

  def update(sym: Symbols, f: Fields, ee2: SetExpr, heap: SHeap): String \/ SHeap = ???

  def expand(pre: SMem) = {
    val (newspatial, newqspatial) = pre.heap.qspatial.foldLeft((pre.heap.spatial, Set[(Symbols, SetExpr, Spatial)]())) {
      (part : (Spatial, Set[(Symbols, SetExpr, Spatial)]), qs : (Symbols, SetExpr, Spatial)) => qs._2 match {
          // TODO: Use String \/ - instead
        case SetLit(as @_*) =>
          // TODO: Consider a good way to merge things
          (as.map(_.asInstanceOf[Symbol]).map(sym => qs._3.subst(Symbol(qs._1), sym)).fold(part._1)(_ ++ _), part._2)
        case _ => (part._1, part._2 + qs)
      }
    }
    SMem(pre.stack, SHeap(newspatial, newqspatial, pre.heap.pure))
  }

  def execute(pres : Set[SMem], c : Statement) : String \/ Set[SMem] = {
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
          val ecs    = cs.map(p => (evalBoolExpr(pre.stack, p._1), p._2))
          val newecs = ecs :+ (for {
            other <- ecs.map(_._1).toList.sequence[StringE, BoolExpr]
          } yield And(other.map(Not) :_*) -> StmtSeq())
          (for {
            cstmt <- ecs
            (eb, s) = cstmt
            posts = for {
              eeb <- eb
              res <- execute(Set(SMem(pre.stack, SHeap(pre.heap.spatial, pre.heap.qspatial, pre.heap.pure + eeb))), s)
            } yield res
          } yield posts).toList.sequence[StringE, Set[SMem]].map(_.toSet.flatten)
          }
        case For(x, m, sb) =>  for {
           // TODO: Figure out how to get meaningful set with new symbols that don't point in the heap
            esols <- m match {
              case MSet(e) => mf.findSet(e, beta)
              case Match(e, c) => mf.findSet(e, beta) // TODO do actual matching
              case MatchStar(e, c) => mf.findSet(e, beta) // TODO do actual matching
            }
            res <- (for {
                esol: (Map[Symbols, SetLit], SetLit) <- esols.toSet
                (th, res) = esol
                newpre = th.foldLeft(pre)((mem: SMem, sub: (Symbols, SetLit)) => mem.subst(SetSymbol(sub._1), sub._2))
                newerpre = expand(newpre)
              } yield res.es.toSet.foldLeftM[StringE, Set[SMem]](Set(newerpre)) { (mems : Set[SMem], sym : BasicExpr) =>
                execute(mems.map(mem => SMem(mem.stack + (x -> SetLit(sym)), mem.heap)), sb)
              }).toList.sequence.map(_.toSet.flatten)
        } yield res
        case Fix(e, sb) => {
          def fixEqCase(bmem: SMem): Disjunction[String, Set[SMem]] = {
            execute(Set(bmem), sb).rightMap(mems => mems.map(mem => for {
              eebefore <- evalExpr(bmem.stack, e)
              eeafter <- evalExpr(mem.stack, e)
            } yield SMem(mem.stack,
                SHeap(mem.heap.spatial, mem.heap.qspatial, mem.heap.pure + Eq(eebefore, eeafter)))
            ).toList.sequence[StringE, SMem].map(_.toSet)
            ).flatMap(identity)
          }
          def fixNeqCase(mem: Set[SMem]): String Disjunction Set[SMem] = {
            ???
          }
          fixEqCase(pre)
        }
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
    case And(ps@_*) =>
      for {
        eps <- ps.map(evalBoolExpr(st, _)).toList.sequence[StringE, BoolExpr]
      } yield And(eps :_*)
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

  private val symCounter = Ref(0)

  private def freshSym: Symbols = {
    val old = !symCounter
    symCounter := !symCounter + 1
    old
  }

  private val mf = new ModelFinder(symCounter, defs)


  private val childfields: Set[Fields] = defs.values.flatMap(_.children.map(_._1)).toSet
  private val reffields: Set[Fields]   = defs.values.flatMap(_.refs.map(_._1)).toSet

  {
    val commoncr = childfields intersect reffields
    assert(commoncr.isEmpty, s"There are overlapping names used for fields and references: ${commoncr.mkString(", ")}")
  }
}
