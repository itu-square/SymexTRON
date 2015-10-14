package semantics

import scala.language.postfixOps

import syntax.ast.MatchExpr._
import syntax.PrettyPrinter
import syntax.ast.ConcreteDesc._
import syntax.ast.QSpatial._
import syntax.ast.SHeap._
import syntax.ast.SMem._
import syntax.ast.SpatialDesc._
import helper._
import semantics.Subst._
import syntax.ast._

import scalaz._, Scalaz._
import scalaz.stream._
import scalaz.concurrent.Task

class SymbolicExecutor(defs: Map[Class, ClassDefinition],
                       kappa: Int = 3, delta: Int = 3, beta: Int = 5) {
  private type StringE[B] = String \/ B
  private type TProcess[A] = Process[Task, A]
  private val pmn = helper.processMonad[Nothing]
  private val pmt = helper.processMonad[Task]


  def match_it(set : SetLit, c : Class, heap: SHeap): String \/ SetLit = set.es.toList.traverseU {
    case Symbol(ident) => for {
      symv <- heap.spatial.get(ident).cata(_.right, s"Unknown symbol: $ident".left)
      stc <- subtypes.get(c).cata(cs => (cs + c).right, s"Unknown class: $c".left)
    } yield if (stc.contains(_sd_c.get(symv))) List[BasicExpr](Symbol(ident)) else List()
    case Var(name) => s"Unevaluated var $name".left
  }.map(l => SetLit(l.flatten : _*))

  def descendants_or_self(set : SetLit, heap: SHeap): String \/ SetLit = set.es.toList.traverseU {
    case e@Symbol(ident) => for {
      symv <- heap.spatial.get(ident).cata(_.right, s"Unknown symbol: $ident".left)
      cd <- _sd_concrete.getOption(symv).cata(_.right, s"Not a concrete value: $symv".left)
      res <- cd.children.values.toList.traverseU({
        case chldv: SetLit => descendants_or_self(chldv, heap)
        case e2 => s"Not a concrete set: $e2".left
      }).map(l => l.flatMap(_.es))
    } yield e :: res
    case Var(name) => s"Unevaluated var $name".left
  }.map(l => SetLit(l.flatten :_*))

  def match_star(set : SetLit, c : Class, heap : SHeap): String \/ SetLit =
    for {
      dcs <- descendants_or_self(set, heap)
      m <- match_it(dcs, c, heap)
    } yield m

  def unfold(sym : Symbols, sd : SpatialDesc, heap: SHeap): Process0[String \/ (ConcreteDesc, SHeap)] = {
    def all_children(c : Class) : Map[Fields, (Class, Cardinality)] = {
      val defc = defs(c)
      defc.children ++ defc.supers.map(all_children).foldLeft(Map[Fields, (Class, Cardinality)]())(_ ++ _)
    }
    def all_references(c : Class) : Map[Fields, (Class, Cardinality)] = {
      val defc = defs(c)
      defc.refs ++ defc.supers.map(all_references).foldLeft(Map[Fields, (Class, Cardinality)]())(_ ++ _)
    }
    def freshSetfromCard(c : Cardinality) : List[SetExpr] = {
      c match {
        case Single() => List(SetLit(Symbol(freshSym)))
        case Many() => List(SetSymbol(freshSym))
        case Opt() => List(SetLit(), SetLit(Symbol(freshSym)))
      }
    }

    sd match {
      case AbstractDesc(c, unowned) =>
        for {
           defc <- Process(defs.get(c).cata(_.right, s"Class definition of $c is unknown".left))
           // Type inference is a bit limited for higher-kinded types
           sts <- defc.traverse(dc => Process((subtypes(Class(dc.name)) + Class(dc.name)).toList : _*))(pmn)
           cdc <- sts.traverse[Process0, String, (ConcreteDesc, SHeap)](st => for {
                     chlds <- Process(all_children(st).mapValues(v => freshSetfromCard(v._2)).sequenceU :_*)
                     refs  <- Process(all_references(st).mapValues(v => freshSetfromCard(v._2)).sequenceU :_*)
                     cd = ConcreteDesc(st, chlds, refs)
                     constr = cd.children.foldLeft(Set[BoolExpr]())((constr : Prop, chld : (Fields, SetExpr)) =>
                       constr + Eq(ISect(chld._2, unowned), SetLit()))
                   } yield (cd, (_sh_spatial.modify(_.updated(sym, cd)) `andThen` _sh_pure.modify(_ ++ constr))(heap)))(pmn)
        } yield cdc
      case cd@ConcreteDesc(c, children, refs) => Process((cd, heap).right)
    }
  }

  def unfold_all(syms : SetLit, heap: SHeap): Process0[String \/ SHeap] = {
    syms.es.toList.foldLeft[Process0[String \/ SHeap]](Process(heap.right))((heaps: Process0[String \/ SHeap], b : BasicExpr) => 
      for {
        he <- heaps
        newheaps <- he.flatMap(h => (for {
           sym <- getSymbol(SetLit(b))
           symv <- h.spatial.get(sym).cata(_.right, s"Unknown symbol $sym".left)
           newheaps = unfold(sym, symv, h)
        } yield newheaps)).traverse(identity)(pmn).map(_.flatMap(identity).map(_._2))
      } yield newheaps)
  }

  def concretise(el: SetLit, heap: SHeap): Process[Task, String \/ SHeap] = {
    def concretise_final(el: SetLit, heap: SHeap): Process0[SHeap] = {
      Process((el.es.foldLeft(heap.some) { (h: Option[SHeap], b: BasicExpr) =>
        for {
          hh <- h
          sym <- b match {
            case Symbol(id) => id.some
            case Var(name) => none
          }
          symv <- hh.spatial.get(sym)
          cd <- _sd_concrete.getOption(symv)
          defc <- defs.get(cd.c)
          if defc.children.values.forall(_._2.isOptional)
        } yield _sh_spatial.modify(_.updated(sym, _cd_children.modify(_.mapValues(v => SetLit()))(cd)))(hh)
      }).toSeq : _*)
    }
    // TODO Convert all SetLit to expression
    def concretise_helper(el: SetLit, heap: SHeap, depth: Int): Process[Task, String \/ SHeap] = {
      if (depth <= 0) {
        concretise_final(el, heap).map(_.right)
      }
      else for {
        unfolded <- unfold_all(el, heap)
        res <- unfolded.traverse[TProcess, String, String \/ SHeap](h => {
          val childsyms = el.es.flatMap(e =>
            e.asInstanceOf[Symbol].id.|>(h.spatial.get)
              .flatMap(_sd_concrete.getOption).map(_.children.values).get)
          // Just join everything together
          val joinede = childsyms.foldLeft(SetLit().asInstanceOf[SetExpr])(Union)
          for {
            joinedset_th <- mf.findSet(joinede, beta)
            joinedset_heap = joinedset_th.map(kv =>
              (h.subst_all(kv._1.map(p => (SetSymbol(p._1), p._2))) |> expand, kv._2))
            cfinal = concretise_final(el, h).map(_.right)
            cfurther = joinedset_heap.traverse[TProcess, String, String \/ SHeap](
              ((hhh : SHeap, els : SetLit) => concretise_helper(els, hhh, depth - 1)).tupled).map(_.flatMap(identity))
            concretised <- cfinal ++ cfurther
          } yield concretised
        })(pmt).map(_.flatMap(identity))
      } yield res
    }
    concretise_helper(el, heap, delta)
  }

  def access(sym: Symbols, f: Fields, heap: SHeap): Process0[String \/ (SetExpr, SHeap)] = {
    for {
      symv <- Process(heap.spatial.get(sym).cata(_.right, s"Error, unknown symbol $sym".left))
      unfolded <- symv.traverse(desc => unfold(sym, desc, heap))(pmn).map(_.flatMap(identity))
      res = unfolded.traverseU(unf => {
        val (df, newheap) = unf
        if (childfields.contains(f))
          for (chld <- df.children.get(f)) yield (chld, newheap)
        else if (reffields.contains(f))
          for (ref <- df.refs.get(f)) yield (ref, newheap)
        else none
      }.cata(_.right, s"No value for field $f".left))
    } yield res.flatMap(identity)
  }

  def disown(heap: SHeap, ee: SetExpr) : SHeap = {
    def disownSD(sym: Symbols, desc: SpatialDesc): SHeap => SHeap  = desc match {
      case AbstractDesc(c, unowned) => _sh_spatial.modify(_.updated(sym, AbstractDesc(c, Union(unowned, ee))))
      case ConcreteDesc(c, children, refs) => _sh_pure.modify(_ ++ (children.foldLeft(Set[BoolExpr]())(
                                                                 (cstr : Prop, chld : (String, SetExpr)) => cstr + Eq(ISect(chld._2, ee), SetLit())))) 
    }
    // TODO consider types when disowning things
    (((h : SHeap) => h.spatial.foldLeft(identity[SHeap] _)((f : SHeap => SHeap, el : (Symbols, SpatialDesc)) =>
        f `andThen` (disownSD _).tupled(el))(h)) `andThen`
      _sh_qspatial.modify(_.map(_qs_unowned.modify(Union(_ ,ee))))) (heap)
  }

  def update(sym: Symbols, f: Fields, ee2: SetExpr, heap: SHeap): Process0[String \/ SHeap] = {
    for {
      symv <- Process(heap.spatial.get(sym).cata(_.right, s"Error, unknown symbol $sym".left))
      unfolded <- symv.traverse(desc => unfold(sym, desc, heap))(pmn).map(_.flatMap(identity))
      res = unfolded.traverseU(unf => {
        val (df, newheap) = unf
        if (childfields.contains(f)) for {
          _ <- df.children.get(f).cata(_.right, s"Error, field $f not allocated for symbol $sym".left)
        } yield _sh_spatial.modify(_.updated(sym, _cd_children.modify(_.updated(f, ee2))(df)))(disown(newheap, ee2))
        else if (reffields.contains(f)) for {
          _ <- df.refs.get(f).cata(_.right, s"Error, field $f not allocated for symbol $sym".left)
        } yield _sh_spatial.modify(_.updated(sym, _cd_refs.modify(_.updated(f, ee2))(df)))(newheap)
        else s"Field $f is neither a child nor a reference field".left
      })
    } yield res.flatMap(identity)
  }

  def expand(heap: SHeap): SHeap = {
    val (newspatial, newqspatial) = heap.qspatial.foldLeft((heap.spatial, Set[QSpatial]())) {
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
    SHeap(newspatial, newqspatial, heap.pure)
  }

  def execute(pres : Process[Task, String \/ SMem], c : Statement) : Process[Task, String \/ SMem] = {
    pres.map[String \/ Set[SMem], Set[String \/ Set[SMem]]] { pre: SMem =>
      c match {
        case StmtSeq(ss@_*) => ss.toList.foldLeftM[StringE, Set[SMem]](Set(pre))(execute)
        case AssignVar(x, e) => for {
          ee <- evalExpr(pre.stack, e)
        } yield Set(SMem(pre.stack + (x -> ee), pre.heap))
        case New(x, c) => for {
          cdef <- defs.get(c).cata(_.right, s"Unknown class: $c".left)
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
            other <- ecs.map(_._1).toList.sequenceU
          } yield And(other.map(Not) :_*) -> StmtSeq())
          (for {
            cstmt <- ecs
            (eb, s) = cstmt
            posts = for {
              eeb <- eb
              res <- execute(Set(SMem(pre.stack, SHeap(pre.heap.spatial, pre.heap.qspatial, pre.heap.pure + eeb))), s)
            } yield res
          } yield posts).toSet.sequenceU.map(_.flatten)
          }
        case For(x, m, sb) =>  for {
           // TODO: Figure out how to get meaningful set with new symbols that don't point in the heap
            esols <- for {
               ee <- evalExpr(pre.stack, _me_e.get(m))
               res <- mf.findSet(ee, beta)
             } yield res
            res <- esols.traverseU(esol => {
                val (th, res) = esol
                val newpre = pre.subst_all(th.map(kv => (SetSymbol(kv._1), kv._2))) |> _sm_heap.modify(expand)
                val mres  = m match {
                  case MSet(e) => Set((res, newpre)).right
                  case Match(e, c) => for {
                     heaps <- unfold_all(res, newpre.heap)
                     res <- heaps.traverseU(h => for {
                      matches <- match_it(res, c, h)
                     } yield (matches, h))
                  } yield res.map(p => (p._1, _sm_heap.set(p._2)(newpre)))
                  case MatchStar(e, c) => for {
                    heaps <- concretise(res, newpre.heap)
                    res <- heaps.traverseU(h => for {
                      matches <- match_star(res, c, h)
                     } yield (matches, h))
                  } yield res.map(p => (p._1, _sm_heap.set(p._2)(newpre)))
                }
               for {
                mr <- mres
                res <- mr.traverseU({
                (syms : SetLit, mem : SMem) => syms.es.toSet.foldLeftM[StringE, Set[SMem]](Set(mem)) {
                 (mems : Set[SMem], sym : BasicExpr) =>  execute(mems.map(_sm_stack.modify(_ + (x -> SetLit(sym)))), sb)
                }}.tupled).map(_.flatten)
              } yield res
              }).map(_.flatten)
        } yield res
        case Fix(e, sb) => {
          def fixEqCase(bmem: SMem): String \/ Set[SMem] = {
            execute(Set(bmem), sb).flatMap(mems => mems.traverseU(mem => for {
              eebefore <- evalExpr(bmem.stack, e)
              eeafter <- evalExpr(mem.stack, e)
            } yield SMem(mem.stack,
                SHeap(mem.heap.spatial, mem.heap.qspatial, mem.heap.pure + Eq(eebefore, eeafter)))
            ))
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
              res <- amems.sequenceU.map(_.flatten)
            } yield res
          }
          fixNeqCase(pre, kappa)
        }
      }
    }.foldLeft((Set[SMem]()).right[String]) { (acc, el) =>
      for (acc_ <- acc; el_ <- el) yield acc_ ++ el_
    }
  }

  def getSymbol(e : SetExpr): String \/ Symbols = {
    e match {
      case SetLit(Symbol(sym)) => sym.right
      case _ => s"${PrettyPrinter.pretty(e)} is not a symbol".left
    }
  }

  def evalBasicExpr(s: SStack, e: BasicExpr): String \/ BasicExpr = e match {
    case Symbol(id) => Symbol(id).right
    case Var(name) =>
      s.get(name).cata({
            case SetLit(evalue) => evalue.right
            case ee => s"Not a basic expression: $ee".left
        }, s"Error while evaluating expression $e".left) 
  }

  def evalExpr(s : SStack, e : SetExpr) : String \/ SetExpr = {
      e match {
        case SetLit(es @ _*) =>
          for {
            ees <- es.toList.traverseU(e => evalBasicExpr(s, e))
          } yield SetLit(ees : _*)
        case SetSymbol(ident) => SetSymbol(ident).right
        case SetVar(name) =>
          s.get(name).cata(_.right, s"Error while evaluating expression $e".left)
        case Diff(e1, e2) => for {
          ee1 <- evalExpr(s, e1)
          ee2 <- evalExpr(s, e2)
        } yield Diff(ee1, ee2)
        case Union(e1, e2) => for {
          ee1 <- evalExpr(s, e1)
          ee2 <- evalExpr(s, e2)
        } yield Union(ee1, ee2)
        case ISect(e1, e2) => for {
          ee1 <- evalExpr(s, e1)
          ee2 <- evalExpr(s, e2)
        } yield ISect(ee1, ee2)
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
        eps <- ps.map(evalBoolExpr(st, _)).toList.sequenceU
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


  private val childfields: Set[Fields] = defs.values.flatMap(_.children.keys).toSet
  private val reffields: Set[Fields]   = defs.values.flatMap(_.refs.keys).toSet
  private val subtypes: Map[Class, Set[Class]] = defs.mapValues(_ => Set[Class]()) ++ {
    defs.values.foldLeft(Map[Class, Set[Class]]())((m : Map[Class, Set[Class]], cd: ClassDefinition) =>
      cd.supers.foldLeft(m)((m_ : Map[Class, Set[Class]], sup : Class) => m_.adjust(sup)(_ + Class(cd.name)))
    ).trans
  }

  {
    val commoncr = childfields intersect reffields
    assert(commoncr.isEmpty, s"There are overlapping names used for fields and references: ${commoncr.mkString(", ")}")
  }
}
