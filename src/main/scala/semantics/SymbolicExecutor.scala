package semantics

/*
Based on "Symbolic Execution with Separation Logic" by Berdine et al. (2005)
 */

import helper._
import syntax.ast._

import scalaz._, Scalaz._
import scalaz.\/.{left, right}

class SymbolicExecutor(defs: Map[Sort, SortDefinition]) {

  def check(pres : Set[SymbolicMemory], c : Command, posts: Set[SymbolicMemory]) : String \/ Unit = for {
    posts_ <- execute(pres, c)
    _ <- SymbolicHeapChecker.==>(posts_, posts).fold[String \/ Unit](cex =>
      left(s"Error, could not find a valid implication for symbolic state $cex attained after execution)"),
      right)
    } yield ()

  def execute(pres : Set[SymbolicMemory], c : Command) : String \/ Set[SymbolicMemory] = {
    // Inconsistent precondition
    if (pres exists (pre => SymbolicHeapChecker.incon(pre.heap))) right(Set())
    else pres.map[String \/ Set[SymbolicMemory], Set[String \/ Set[SymbolicMemory]]] { pre: SymbolicMemory =>
      c match {
        case Fail() => left("Error because of reachable _fail_ command")
        case CSeq(cs @ _*) =>
          cs.foldLeft(right[String, Set[SymbolicMemory]](Set(pre))) { (acc, c) =>
            for {
              newpres <- acc
              posts <- execute(newpres, c)
            } yield posts
          }
        case AssignVar(x, e) =>
          for {
            ee <- evalExpr(pre.stack, e)
            post = SymbolicMemory(pre.stack + (x -> ee), pre.heap)
          } yield Set(post)
        case LoadField(x, e, f) =>
            for {
              ee <- evalExpr(pre.stack, e)
              posts <- (for {
                  spu <- pre.heap.spatial.merge
                  efss <- spu.get(ee)
                  (efs, _) = efss
                  fv <- efs.get(f)
                } yield fv).fold[String \/ Set[SymbolicMemory]](left(s"Error while loading field $f of symbol $e")) {
                    fv =>
                      val post = SymbolicMemory(pre.stack + (x -> fv), pre.heap)
                      right(Set(post))
                }
            } yield posts
        case New(x, s) =>
          (defs get s).fold[String \/ Set[SymbolicMemory]](left(s"Error, unknown sort $s")) { sdef =>
              val alpha = freshSym()
              val newsh = SymbolicHeap(pre.heap.pure + SortMem(Symbol(alpha), s),
                pre.heap.spatial +
                  (Symbol(alpha) -> Set(((sdef.children ++ sdef.refs map
                      (f => (f._1, SetE()))), Unowned()))),
                  pre.heap.preds)
              val post = SymbolicMemory(pre.stack + (x -> Symbol(alpha)), newsh)
              right(Set(post))
          }
        case AssignField(e1, f, e2) =>
          for {
            ee1 <- evalExpr(pre.stack, e1)
            ee2 <- evalExpr(pre.stack, e2)
            s1 <- SymbolicHeapChecker.sortOf(pre, ee1)
            s2 <- SymbolicHeapChecker.sortOf(pre, ee2)
            s1def <- (defs get s1).fold[String \/ SortDefinition](left(s"Error, unknown sort $s1"))(right)
            fIsChild = s1def.children.contains(f)
            fIsReference = s1def.children.contains(f)
            res <- if (fIsChild) assignChild(ee1, f, ee2, pre)
                 else if (fIsReference) assignReference(ee1, f, ee2, pre)
                 else left(s"Error, $f is neither a child nor reference")
          } yield res
        case If(cs) =>
          for {
            cs_ <- cs.map(chc => {
                for {
                  eei <- evalSimpleProp(pre.stack, chc._1)
                  res =  if (SymbolicHeapChecker.oracle(pre.heap,
                                        SymbolicHeap(Set(not(eei)), pre.heap.spatial, pre.heap.preds))) None
                         else Some(eei, chc._2)
                } yield res
              }).foldLeft(right[String, Set[Option[(SimpleProp, Command)]]](Set()))((acc, el) => {
                for {
                  acc_ <- acc
                  el_  <- el
                } yield acc_ + el_
              }).map(_.filter(_.isDefined).map(_.get))
            posts <- {
              cs_.map[String \/ Set[SymbolicMemory], Set[String \/ Set[SymbolicMemory]]] { eci =>
                val (ei : SimpleProp, ci : Command) = eci
                val newpre = SymbolicMemory(pre.stack,
                                  SymbolicHeap(pre.heap.pure + ei, pre.heap.spatial, pre.heap.preds))
                execute(Set(newpre), ci)
              }.foldLeft(right[String, Set[SymbolicMemory]](Set()))((acc, el) =>
                 for {
                   acc_ <- acc
                   el_ <- el
                 } yield acc_ ++ el_)
            }
          } yield posts
        case For(x, s, e, inv, cb) => ???
        case ForMatch(x, s, e, inv, cb) => ???
        case Fix(e, inv, cb) => ???
      }
    }.foldLeft(right[String, Set[SymbolicMemory]](Set())) { (acc, el) =>
      for (acc_ <- acc; el_ <- el) yield acc_ ++ el_
    }
  }

  def assignChild(ee1: Expr, f: Fields, ee2: Expr, pre: SymbolicMemory) = {
    val spatial = pre.heap.spatial
    for {
      spm  <- spatial.merge.cata(right, left("Error, inconsistent heap"))
      e1fss <- spm.get(ee1).cata(right, left(s"Error, $ee1 not allocated"))
      (e1fs, own1) = e1fss
      fv1 <- e1fs.get(f).cata(right, left(s"Error, no field $f of $ee1"))
      e2fss <- spm.get(ee2).cata(right, left(s"Error, $ee2 not allocated"))
      (e2fs, own2) = e2fss
      post <- {
        var newspatial = spm
        for {
         _ <- own2 match {
            case Unowned () => right (())
            case Owned (owner@Symbol (ident), frev) =>
            for {
              own2fss <- spm.get (owner).cata (right, left (s"Error, owner of $ee2 not allocated"))
              (own2fs, own2owner) = own2fss
            } yield right {
                newspatial = newspatial.updated (owner, (own2fs.updated (frev, SetE ()), own2owner))
            }
          }
         _ <- fv1 match {
           case Symbol(ident) => for {
             fv1fss <- spm.get(fv1).cata(right, left(s"Error, $ee1.$f not allocated"))
             (fv1fs, f1owner) = fv1fss
           } yield {
               newspatial = newspatial.updated(fv1, (fv1fs, Unowned()))
             }
           case SetE() => right(())
           case Var(x) => left(s"Error, unevaluated variable $x")
           case Union(_,_) | Diff(_,_) | ISect(_,_) | SetE(_*) =>
             left(s"Error, assigning to a field containing a set of items") //TODO: Support assignment to child sets in the future
         }
         _ <- right {
           newspatial = newspatial.updated(ee1, (e1fs.updated(f, ee2), own1))
           // It is important to use Map(k -> v) ++ m instead of m.updated(k, v), due to equality
         }
         _ <- ee1 match {
           case ee1@Symbol(ident) => right {
             newspatial = newspatial.updated(ee2, (e2fs, Owned(ee1, f)))
           }
           case Var(x) => left(s"Error, unevaluated variable $x")
           case Union(_,_) | Diff(_,_) | ISect(_,_) | SetE(_*) =>
             left(s"Error, assigning to a set of items") //TODO: Support assignment to child sets in the future
         }
        } yield {
          val post = SymbolicMemory(pre.stack,
                        SymbolicHeap(pre.heap.pure, newspatial map (p => (p._1, Set(p._2))) , pre.heap.preds))
          Set(post)
        }
      }
    } yield post
  }

  def assignReference(ee1: Expr, f: Fields, ee2: Expr, pre: SymbolicMemory): String \/ Set[SymbolicMemory] = {
    val spatial = pre.heap.spatial
    val e1fs = spatial.get(ee1)
    e1fs.fold[String \/ Set[SymbolicMemory]](left(s"Error, $ee1 not allocated"))(e1fs => {
      val newspatial = spatial.updated(ee1, e1fs.map(m => (m._1.updated(f, ee2), m._2)))
      val post = SymbolicMemory(pre.stack, SymbolicHeap(pre.heap.pure, newspatial, pre.heap.preds))
      right(Set(post))
    })
  }


    def evalExpr(s : SymbolicStack, e : Expr) : String \/ Expr = {
      type StringE[B] = String \/ B
      e match {
        case SetE(es @ _*) =>
          for {
            ees <- es.toList.traverse[StringE, Expr](e => evalExpr(s, e))
          } yield SetE(ees.map(_.asInstanceOf[BasicExpr]) : _*)
        case Symbol(ident) => right(Symbol(ident))
        case Var(name) =>
          // Scalas type inference is really primitive...
          s.get(name).fold[String \/ Expr](left(s"Error while evaluating expression $e"))(right)
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
      }
    }
  
  def evalSimpleProp(st : SymbolicStack, sp : SimpleProp) : String \/ SimpleProp = sp match {
    case Eq(e1, e2) =>
      for {
        ee1 <- evalExpr(st, e1)
        ee2 <- evalExpr(st, e2)
      } yield Eq(ee1, ee2)
    case SortMem(e1, s) =>
      for {
        ee1 <- evalExpr(st, e1)
      } yield SortMem(ee1, s)
    case Not(p) =>
      for {
        ep <- evalSimpleProp(st, p)
      } yield Not(ep)
    case SetMem(e1, e2) =>
      for {
        ee1 <- evalExpr(st, e1)
        ee2 <- evalExpr(st, e2)
      } yield SetMem(ee1.asInstanceOf, ee2)
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

  private var symCounter = 0

  private def freshSym(): Symbols = {
    symCounter += 1
    symCounter
  }
}
