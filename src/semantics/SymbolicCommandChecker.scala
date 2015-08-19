package semantics

/*
Based on "Symbolic Execution with Separation Logic" by Berdine et al. (2005)
 */

import helper._
import syntax.ast._

import scalaz.\/
import scalaz.\/.{left, right}

class SymbolicCommandChecker(defs: Map[Sort, SortDefinition]) {

  def check(pres : Set[SymbolicMemory], c : Command, posts: Set[SymbolicMemory]) : String \/ Unit = for {
    posts_ <- execute(pres, c)
    _ <- SymbolicHeapChecker.==>(posts_, posts).fold[String \/ Unit](cex =>
      left(s"Error, could not find a valid implication for symbolic state $cex attained after execution)"),
      right (_))
    } yield ()

  def execute(pres : Set[SymbolicMemory], c : Command) : String \/ Set[SymbolicMemory] = {
    // Inconsistent precondition
    if (pres exists (pre => SymbolicHeapChecker.incon(pre.heap))) right(Set())
    else pres.map[String \/ Set[SymbolicMemory], Set[String \/ Set[SymbolicMemory]]] { pre: SymbolicMemory =>
      c match {
        case Skip() => right(Set(pre))
        case Fail() => left("Error because of reachable _fail_ command")
        case Seq(c1, c2) =>
          for {
            newpres <- execute(Set(pre), c1)
            posts <- execute(newpres, c2)
          } yield posts
        case AssignVar(x, e) =>
          for {
            ee <- (evalExpr(pre.stack, e))
            post = SymbolicMemory(pre.stack + (x -> ee), pre.heap)
          } yield Set(post)
        case Load(x, e, f) =>
            for {
              ee <- evalExpr(pre.stack, e)
              posts <- (for {
                  spu <- pre.heap.spatial.merge
                  efs <- spu.get(ee)
                  fv <- efs.get(f)
                } yield fv).fold[String \/ Set[SymbolicMemory]](left(s"Error while loading field $f of symbol $e")) {
                    fv =>
                      val post = SymbolicMemory(pre.stack + (x -> fv), pre.heap)
                      right(Set(post))
                }
            } yield posts
        case New(x, s) => {
          (defs get s).fold[String \/ Set[SymbolicMemory]](left(s"Error, unknown sort $s")) { sdef =>
              val alpha = freshSym()
              val newsh = SymbolicHeap(pre.heap.pure + SortMem(Symbol(alpha), s),
                pre.heap.spatial +
                  (Symbol(alpha) -> Set((sdef.children ++ sdef.fields).mapValues(_ => Nil()) + ("@owner" -> Nil()))))
              val post = SymbolicMemory(pre.stack + (x -> Symbol(alpha)), newsh)
              right(Set(post))
          }
        }
        case AssignField(e1, f, e2) => {
          for {
            ee1 <- evalExpr(pre.stack, e1)
            ee2 <- evalExpr(pre.stack, e2)
            s1 <- SymbolicHeapChecker.sortOf(pre, ee1)
            s2 <- SymbolicHeapChecker.sortOf(pre, ee2)
            s1def <- (defs get s1).fold[String \/ SortDefinition](left(s"Error, unknown sort $s1"))(right(_))
            fIsChild = s1def.children.contains(f)
            fIsReference = s1def.children.contains(f)
            res <- if (fIsChild) assignChild(ee1, f, ee2, pre)
                 else if (fIsReference) assignReference(ee1, f, ee2, pre)
                 else left(s"Error, $f is neither a child nor reference")
          } yield res
        }
        case If(cs) => {
          for {
            cs_ <- cs.map(p => {
                val (ei, ci) = p
                for {
                  eei <- evalSimpleProp(pre.stack, ei)
                  res =  if (SymbolicHeapChecker.oracle(pre.heap, SymbolicHeap(Set(not(eei)), pre.heap.spatial))) None
                         else Some(eei, ci)
                } yield res
              }).foldLeft(right[String, Set[Option[(SimpleProp[TRUE.V], Command)]]](Set()))((acc, el) => {
                for {
                  acc_ <- acc
                  el_  <- el
                } yield (acc_ + el_)
              }).map(_.filter(_.isDefined).map(_.get))
            posts <- {
              cs_.map[String \/ Set[SymbolicMemory], Set[String \/ Set[SymbolicMemory]]] { eci =>
                val (ei : SimpleProp[TRUE.V], ci : Command) = eci
                val newpre = SymbolicMemory(pre.stack, SymbolicHeap(pre.heap.pure + ei, pre.heap.spatial))
                execute(Set(newpre), ci)
              }.foldLeft(right[String, Set[SymbolicMemory]](Set()))((acc, el) =>
                 for {
                   acc_ <- acc
                   el_ <- el
                 } yield (acc_ ++ el_))
            }
          } yield posts
        }
        case For(x, s, e, inv, cb) => ???
        case ForMatch(x, s, e, inv, cb) => ???
        case Fix(e, inv, cb) => ???
      }
    }.foldLeft(right[String, Set[SymbolicMemory]](Set())) { (acc, el) =>
      for (acc_ <- acc; el_ <- el) yield (acc_ ++ el_)
    }
  }

  def assignChild(ee1: Expr[TRUE.type], f: Fields, ee2: Expr[TRUE.type],
                  pre: SymbolicMemory) = {
    val spatial = pre.heap.spatial
    (for {
      spm <- spatial.merge
      res =
        (for {
          e1fs <- spm.get(ee1)
          fv <- e1fs.get(f)
        } yield (e1fs, fv)).fold[String \/ Set[SymbolicMemory]](left(s"Error, $ee1.$f not allocated"))(mi1 => {
          val (e1fs, fv1) = mi1
          (for {
            e2fs <- spm.get(ee2)
            own2 <- e2fs.get("@owner")
          } yield (e2fs, own2)).fold[String \/ Set[SymbolicMemory]](left(s"Error, $ee2 not allocated"))(mi2 => {
            val (e2fs, own2) = mi2
            var newspatial = spatial
            for {
              _ <- own2 match {
                case Nil() => right(())
                case Symbol(id) =>
                  for {
                    sown2 <- SymbolicHeapChecker.sortOf(pre, own2)
                    sown2def <- (defs get sown2).fold[String \/ SortDefinition](
                      left(s"Error, unknown sort $sown2"))(right(_))
                    _ <- (for {
                      own2fs <- spm.get(own2)
                      f2 <- own2fs.find(p => sown2def.children.contains(p._1) && p._2 == ee2).map(p => p._1)
                    } yield (own2fs, f2)).fold[String \/ Unit](left(s"Error, cannot find a child field of $own2 that " +
                      s"refers to $ee2"))(owf => right {
                      newspatial = newspatial.updated(own2, Set(owf._1.updated(owf._2, Nil())))
                    })
                  } yield ()
              }
              _ <- fv1 match {
                case Nil() => right(())
                case Symbol(id) =>
                  spm.get(fv1).fold[String \/ Unit](left(s"Error, $fv1 not allocated"))(fv1fs => right {
                    newspatial = newspatial.updated(fv1, Set(fv1fs.updated("@owner", Nil())))
                  })
              }
              _ <- right {
                newspatial = newspatial.updated(ee1, Set(e1fs.updated(f, ee2)))
                newspatial = newspatial.updated(ee2, Set(e2fs.updated("@owner", ee1)))
              }
            } yield ()
            val post = SymbolicMemory(pre.stack, SymbolicHeap(pre.heap.pure, newspatial))
            right(Set(post))
          })
        })
    } yield res).fold[String \/ Set[SymbolicMemory]](left(s"Error, inconsistent heap"))(identity)
  }

  def assignReference(ee1: Expr[TRUE.type], f: Fields, ee2: Expr[TRUE.type],
                      pre: SymbolicMemory): String \/ Set[SymbolicMemory] = {
    val spatial = pre.heap.spatial
    val e1fs = spatial.get(ee1)
    e1fs.fold[String \/ Set[SymbolicMemory]](left(s"Error, $ee1 not allocated"))(e1fs => {
      val newspatial = spatial.updated(ee1, e1fs.map(m => m.updated(f, ee2)))
      val post = SymbolicMemory(pre.stack, SymbolicHeap(pre.heap.pure, newspatial))
      right(Set(post))
    })
  }


    def evalExpr[B <: BOOL](s : SymbolicStack, e : Expr[B]) : String \/ Expr[TRUE.V] = {
      e match {
        case Nil() => right(Nil())
        case Symbol(id) => right(Symbol(id))
        case Var(name) =>
          // Scalas type inference is really primitive...
          s.get(name).fold[String \/ Expr[TRUE.V]](left(s"Error while evaluating expression $e"))(right(_))
      }
    }
  
  def evalSimpleProp[B <: BOOL](st : SymbolicStack, sp : SimpleProp[B]) : String \/ SimpleProp[TRUE.V] = {
    sp match {
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
    }
  }

  private var symCounter = 0

  private def freshSym(): Symbols = {
    symCounter += 1
    symCounter
  }
}
