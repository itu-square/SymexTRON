package semantics

/*
Based on "Symbolic Execution with Separation Logic" by Berdine et al. (2005)
 */

import helper._
import syntax.ast._

import scalaz.\/
import scalaz.\/.{left, right}

class SymbolicCommandChecker(defs: Map[Sort, SortDefinition]) {

  def check(pres : Set[SymbolicMemory], c : Command, posts: Set[SymbolicMemory]) : String \/ Unit = {
    // Inconsistent precondition
    if (pres exists (pre => SymbolicHeapChecker.incon(pre.heap))) right()
    else pres.map[String \/ Unit, Set[String \/ Unit]] { pre: SymbolicMemory =>
      c match {
        case Skip() =>
          if (posts forall (post => SymbolicHeapChecker.oracle(pre.heap, post.heap))) right()
          else left("")
        case Fail() => left("Error because of reachable _fail_ command")
        case AssignVar(x, e, c) =>
          for {
            ee <- (eval(pre.stack, e))
            newpre = SymbolicMemory(pre.stack + (x -> ee), pre.heap)
            _ <- check(Set(newpre), c, posts)
          } yield ()
        case Load(x, e, f, c) =>
            for {
              ee <- eval(pre.stack, e)
              _ <- (for {
                  spu <- pre.heap.spatial.merge
                  efs <- spu.get(ee)
                  fv <- efs.get(f)
                } yield fv).fold[String \/ Unit](left(s"Error while loading field $f of symbol $e")) { fv =>
                    val newpre = SymbolicMemory(pre.stack + (x -> fv), pre.heap)
                    check(Set(newpre), c, posts)
                }
            } yield ()
        case New(x, s, c) => {
          (defs get s).fold[String \/ Unit](left(s"Error, unknown sort $s")) { sdef =>
              val alpha = freshSym()
              val newsh = SymbolicHeap(pre.heap.pure + SortMem(Symbol(alpha), s),
                pre.heap.spatial +
                  (Symbol(alpha) -> Set((sdef.children ++ sdef.fields).mapValues(_ => Nil()) + ("@owner" -> Nil()))))
              val newpre = SymbolicMemory(pre.stack + (x -> Symbol(alpha)), newsh)
              check(Set(newpre), c, posts)
          }
        }
        case AssignField(e1, f, e2, c) => {
          for {
            ee1 <- eval(pre.stack, e1)
            ee2 <- eval(pre.stack, e2)
            s1 <- SymbolicHeapChecker.sortOf(pre, ee1)
            s2 <- SymbolicHeapChecker.sortOf(pre, ee2)
            s1def <- (defs get s1).fold[String \/ SortDefinition](left(s"Error, unknown sort $s1"))(right(_))
            s2def <- (defs get s2).fold[String \/ SortDefinition](left(s"Error, unknown sort $s2"))(right(_))
            fIsChild : Boolean <- s1def.children.contains(f)
            fIsReference : Boolean <- s1def.children.contains(f)
            if fIsChild || fIsReference
            _ <- if (fIsChild) assignChild(s2def, ee1, f, ee2, c) else assignReference(s2def, ee1, f, ee2, c)
          } yield ()
        }
        case If(p, cs, c) => ???
        case For(x, s, e, inv, cb, c) => ???
        case ForMatch(x, s, e, inv, cb, c) => ???
      }
    }.fold(right())((p1, p2) => p1.fold(left(_), _ => p2))
  }

  def assignChild(s2def: SortDefinition, ee1: Expr[TRUE.type], f: Fields, ee2: Expr[TRUE.type], c: Command) = ???

  def assignReference(s2def: SortDefinition, ee1: Expr[TRUE.type], f: Fields, ee2: Expr[TRUE.type], c: Command) = ???


    def eval[B <: BOOL](s : SymbolicStack, e : Expr[B]) : String \/ Expr[TRUE.V] = {
      e match {
        case Nil() => right(Nil())
        case Symbol(id) => right(Symbol(id))
        case Var(name) =>
          // Scalas type inference is really primitive...
          s.get(name).fold[String \/ Expr[TRUE.V]](left(s"Error while evaluating expression $e"))(right(_))
      }
    }

  private var symCounter = 0

  private def freshSym(): Symbols = {
    symCounter += 1
    symCounter
  }
}
