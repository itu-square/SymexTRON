package semantics

/*
Based on "Symbolic Execution with Separation Logic" by Berdine et al. (2005)
 */

import _root_.syntax.ast.ClassDefinition._
import _root_.syntax.ast.ConcreteDesc._
import _root_.syntax.ast.QSpatial._
import _root_.syntax.ast.SHeap._
import _root_.syntax.ast.SMem._
import _root_.syntax.ast.SpatialDesc._
import _root_.syntax.{ast, PrettyPrinter}
import helper._
import monocle.Getter
import syntax.ast._

import scalaz._, Scalaz._
import scalaz.\/.{left, right}
import Subst._
import language.postfixOps

class SymbolicExecutor(defs: Map[Class, ClassDefinition],
                       kappa: Int = 3, delta: Int = 3, beta: Int = 5) {
  private type StringE[B] = String \/ B

  def unfold(sd : SpatialDesc): String \/ Set[(ConcreteDesc, Prop)] = {
    def all_children(c : Class) : Map[Fields, Class] = {
      val defc = defs(c)
      defc.children ++ defc.supers.map(all_children).foldLeft(Map[Fields, Class]())(_ ++ _)
    }
    def all_references(c : Class) : Map[Fields, Class] = {
      val defc = defs(c)
      defc.children ++ defc.supers.map(all_children).foldLeft(Map[Fields, Class]())(_ ++ _)
    }
    sd match {
      case AbstractDesc(c, unowned) => for {
        defc <- defs.get(c).cata(right, left(s"Class definition of $c is unknown"))
        sts = subtypes(Class(defc.name))
      } yield for {
          st <- sts
        } yield (ConcreteDesc(c, all_children(c).mapValues(_ => SetSymbol(freshSym)),
                    all_references(c).mapValues(_ => SetSymbol(freshSym))), Set[BoolExpr]())
      // TODO Actually add unonwed constraints
      case cd@ConcreteDesc(c, children, refs) => right(Set((cd, Set[BoolExpr]())))
    }
  }

  //TODO Unfold fields when having abstract desc for access and update
  def access(sym: Symbols, f: Fields, heap: SHeap): String \/ Set[(SetExpr, SHeap)] = {
    for {
      symv <- heap.spatial.get(sym).cata(right, left(s"Error, unknown symbol $sym"))
      unfolded <- unfold(symv)
      res <- unfolded.map(unf => {
        val (df, constr) = unf
        val newheap = (_sh_spatial.modify(_.updated(sym, df)) `andThen` _sh_pure.modify(_ ++ constr))(heap)
        if (childfields.contains(f))
          for (chld <- df.children.get(f)) yield (chld, newheap)
        else if (reffields.contains(f))
          for (ref <- df.refs.get(f)) yield (ref, newheap)
        else none
      }.cata(right, left(s"No value for field $f"))).toList.sequence[StringE, (SetExpr, SHeap)].map(_.toSet)
    } yield res
  }

  def disown(heap: SHeap, ee: SetExpr) : SHeap = {
    def disownSD(desc: SpatialDesc): SpatialDesc = desc match {
      case AbstractDesc(c, unowned) => AbstractDesc(c, Union(unowned, ee))
      case ConcreteDesc(c, children, refs) => ConcreteDesc(c, children.mapValues(Diff(_, ee)), refs)
    }
    // TODO consider types when disowning things
    (_sh_spatial.modify(_.mapValues(disownSD)) `andThen`
      _sh_qspatial.modify(_.map(_qs_unowned.modify(Union(_ ,ee))))) (heap)
  }

  def update(sym: Symbols, f: Fields, ee2: SetExpr, heap: SHeap): String \/ Set[SHeap] = {
    for {
      symv <- heap.spatial.get(sym).cata(right, left(s"Error, unknown symbol $sym"))
      unfolded <- unfold(symv)
      res <- unfolded.map(unf => {
        val (df, constr) = unf
        val newheap = (_sh_spatial.modify(_.updated(sym, df)) `andThen` _sh_pure.modify(_ ++ constr))(heap)
        if (childfields.contains(f)) for {
          _ <- df.children.get(f).cata(right, left(s"Error, field $f not allocated for symbol $sym"))
        } yield _sh_spatial.modify(_.updated(sym, _cd_children.modify(_.updated(f, ee2))(df)))(disown(newheap, ee2))
        else if (reffields.contains(f)) for {
          _ <- df.refs.get(f).cata(right, left(s"Error, field $f not allocated for symbol $sym"))
        } yield _sh_spatial.modify(_.updated(sym, _cd_refs.modify(_.updated(f, ee2))(df)))(newheap)
        else left(s"Field $f is neither a child nor a reference field")
      }).toList.sequence[StringE, SHeap].map(_.toSet)
    } yield res
  }

  def expand(pre: SMem) = {
    val (newspatial, newqspatial) = pre.heap.qspatial.foldLeft((pre.heap.spatial, Set[QSpatial]())) {
      (part : (Spatial[Symbols], Set[QSpatial]), qs : QSpatial) => qs.e match {
          // TODO: Use String \/ - instead
        case SetLit(as @_*) =>
          val expanded: Map[Symbols, SpatialDesc] =
            as.map(_.asInstanceOf[Symbol]).map(_.id -> _sd_abstract.reverseGet(AbstractDesc(qs.c, qs.unowned))).toMap
          // TODO: Consider a good way to merge things
          (part._1 ++ expanded, part._2)
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
          sym <- evalExpr(pre.stack, e).flatMap(getSymbol)
          ares <- access(sym, f, pre.heap)
        } yield ares.map(p => SMem(pre.stack + (x -> p._1), p._2))
        case AssignField(e1, f, e2) => for {
          sym <- evalExpr(pre.stack, e1).flatMap(getSymbol)
          ee2 <- evalExpr(pre.stack, e2)
          newheaps <- update(sym, f, ee2, pre.heap)
        } yield newheaps.map(newheap => SMem(pre.stack, newheap))
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
              case MSet(e) =>
               for {
                ee <- evalExpr(pre.stack, e)
                res <- mf.findSet(ee, beta)
               } yield res
              case Match(e, c) =>
               for {
                ee <- evalExpr(pre.stack, e)
                res <- mf.findSet(ee, beta)
               } yield res // TODO: Do actual matchin
             case MatchStar(e, c) =>
               for {
                ee <- evalExpr(pre.stack, e)
                res <- mf.findSet(ee, beta)
               } yield res // TODO: Do actual matching
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
          def fixEqCase(bmem: SMem): String \/ Set[SMem] = {
            execute(Set(bmem), sb).rightMap(mems => mems.map(mem => for {
              eebefore <- evalExpr(bmem.stack, e)
              eeafter <- evalExpr(mem.stack, e)
            } yield SMem(mem.stack,
                SHeap(mem.heap.spatial, mem.heap.qspatial, mem.heap.pure + Eq(eebefore, eeafter)))
            ).toList.sequence[StringE, SMem].map(_.toSet)
            ).flatMap(identity)
          }
          def fixNeqCase(bmem: SMem, k: Int): String \/ Set[SMem] = {
            for {
              imems <- execute(Set(bmem), sb)
              amems = for {
                imem <- imems
                amems = for {
                  eebefore <- evalExpr(bmem.stack, e)
                  eeafter  <- evalExpr(imem.stack, e)
                  newheap = (_sm_heap ^|-> _sh_pure).modify(_ + Not(Eq(eebefore, eeafter))) (imem)
                  amems <- if (k <= 0) fixEqCase(imem) else for {
                      mems2 <- fixEqCase(imem)
                      mems1 <- fixNeqCase(imem, k)
                  } yield mems1 ++ mems2
                } yield amems
              } yield amems
              res <- amems.toList.sequence[StringE, Set[SMem]].rightMap(_.toSet.flatten)
            } yield res
          }
          fixNeqCase(pre, kappa)
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
            case SetLit(evalue) => right(evalue)
            case ee => left(s"Not a basic expression: $ee")
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

  private val symCounter = Counter(0)

  private def freshSym: Symbols = symCounter++

  private val mf = new ModelFinder(symCounter, defs)


  private val childfields: Set[Fields] = defs.values.flatMap(_.children.map(_._1)).toSet
  private val reffields: Set[Fields]   = defs.values.flatMap(_.refs.map(_._1)).toSet
  private val subtypes: Map[Class, Set[Class]] = {
    defs.values.foldLeft(Map[Class, Set[Class]]())((m : Map[Class, Set[Class]], cd: ClassDefinition) =>
      cd.supers.foldLeft(m)((m_ : Map[Class, Set[Class]], sup : Class) => m_.adjust(sup)(_ + Class(cd.name)))
    ).trans
  }


  {
    val commoncr = childfields intersect reffields
    assert(commoncr.isEmpty, s"There are overlapping names used for fields and references: ${commoncr.mkString(", ")}")
  }
}
