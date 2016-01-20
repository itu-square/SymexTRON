package semantics

import java.util

import kodkod.ast._
import kodkod.engine.satlab.SATFactory
import kodkod.engine.{Solution, Solver}
import kodkod.instance.{Bounds, TupleSet, Universe}

import _root_.syntax.ast
import syntax.ast._
import semantics.domains._
import semantics.domains.SpatialDesc._
import semantics.domains.SHeap._
import semantics.domains.SMem._
import semantics.Subst._
import helper._

import scala.collection.JavaConverters._
import scala.collection.mutable
import scalaz._, Scalaz._
import scalaz.concurrent.Task
import scalaz.stream._

import com.typesafe.scalalogging.LazyLogging

class ModelFinder(symcounter: Counter, defs: Map[Class, ClassDefinition],
                  beta: Int, delta: Int)
  extends LazyLogging {
  private type StringE[T] = String \/ T
  private type EvalRes[T] = (Set[Relation], Set[Integer], Formula, T, Map[Symbols, Relation])

  var counter = 0

  val SymbolicSet = Relation.unary("SymbolicSet")
  val syms = Relation.binary("syms")


  val SymbolsRel = Relation.unary("Symbols")
  val name = Relation.binary("name")

  val Types = Relation.unary("Types")
  val isSubType = Relation.binary("isSubType")
  val typeOfS = Relation.binary("typeOfS")
  val typeOf = Relation.binary("typeOf")

  def freshSet : Relation = {
    counter = counter + 1
    Relation.unary(s"ConcreteSymbolicSet$counter")
  }

  def constraints : Formula = {
    val nameTyping = {
      val s = Variable.unary("s")
      (s.join(name).one and (s.join(name) in Expression.INTS) forAll (s oneOf SymbolsRel)) and
        (name.join(Expression.UNIV) in SymbolsRel)
    }
    val symsTyping = {
      val ss = Variable.unary("ss")
      ((ss.join(syms) in SymbolsRel) forAll (ss oneOf SymbolicSet)) and
        (syms.join(Expression.UNIV) in SymbolicSet)
    }
    val nameUniqueness = {
      val s1 = Variable.unary("s1")
      val s2 = Variable.unary("s2")
      (s1 eq s2) iff (s1.join(name) eq s2.join(name)) forAll ((s1 oneOf SymbolsRel) and (s2 oneOf SymbolsRel))
    }
    val typeOfSTyping = {
      val ss = Variable.unary("ss")
      (ss.join(typeOfS).one and (ss.join(typeOfS) in Types) forAll (ss oneOf SymbolicSet)) and
        (typeOfS.join(Expression.UNIV) in SymbolicSet)
    }
    val typeOfTyping = {
      val s = Variable.unary("s")
      (s.join(typeOf).one and (s.join(typeOf) in Types) forAll (s oneOf SymbolsRel)) and
        (typeOf.join(Expression.UNIV) in SymbolsRel)
    }
    nameTyping and nameUniqueness and symsTyping //and typeOfTyping and typeOfSTyping
  }


  def bounds(rs : Set[Relation], is : Set[Integer], minSymbols : Int) : Bounds = {
    val symbolintnames = (for (i <- 1 to (minSymbols - is.size)) yield {
      Int.box(symcounter.++)
    }).toSet ++ is

    val symbolids = symbolintnames.toList.sorted.map(i => s"sym'$i")
    val symbolicsets = for ((r, i) <- rs.zipWithIndex) yield (r, s"set'$i")
    val types = (for (c <- defs.keys) yield (c, s"type'${c.name}")).toMap
    val atoms =  symbolintnames ++ symbolids ++ symbolicsets.map(_._2) ++ types.values.toSeq
    val universe = new Universe(atoms.asJava)
    val bounds = new Bounds(universe)
    val f = universe.factory

    bounds.boundExactly(SymbolsRel, f setOf (symbolids :_*))
    for ((r, i) <- symbolicsets) bounds.boundExactly(r, f setOf i)
    bounds.boundExactly(SymbolicSet, f setOf (symbolicsets.map(_._2).toSeq :_*))

    for (symname <- symbolintnames)
      bounds.boundExactly(symname.intValue, f range (f tuple symname, f tuple symname))

    bounds.bound(syms, f allOf 2)
    val nameUpper = f noneOf 2
    for ((sid, sname) <- symbolids.zip(symbolintnames.toList.sorted))
      nameUpper.add((f tuple sid) product (f tuple sname))
    bounds.bound(name, nameUpper)

    bounds.boundExactly(Types, f setOf (types.values.toSeq :_*)) // TODO fix bounds
    val stBounds = f noneOf 2
    for ((c, sc) <- defs.subtypesOrSelf.toList.flatMap { case (c, scs) => scs.toList.map(sc => (c,sc)) }) {
      stBounds.add((f tuple (types(sc))) product (f tuple (types(c))))
    }
    bounds.boundExactly(isSubType, stBounds)
    val typeOfSUpper = f noneOf 2
    for (ss <- symbolicsets.map(_._2).toList) {
      for (typ <- types.values.toList) {
        typeOfSUpper.add((f tuple ss) product (f tuple typ))
      }
    }
    bounds.bound(typeOfS, typeOfSUpper)
    val typeOfUpper = f noneOf 2
    for (sid <- symbolids) {
      for (typ <- types.values.toList) {
        typeOfUpper.add((f tuple sid) product (f tuple typ))
      }
    }
    bounds.bound(typeOf, typeOfUpper)
    bounds
  }

  def evalBoolExpr(b : BoolExpr[IsSymbolic.type], th : Map[Symbols, Relation], isNegated: Boolean = false)
  : String \/ EvalRes[Formula] = b match {
    case Eq(e1, e2) => evalBinaryBoolExpr(e1, _ eq _, e2, th, isNegated)
    case SetMem(e1, e2) => for {
        ee2 <- evalSetExpr(e2, th)
        (rs2, is2, f2, r2, th2) = ee2
        formula = {
          val sym = Variable.unary("sym")
          val x = Variable.unary("x")
          val symInSyms = sym in x.join(syms)
          (e1 match {
            case Symbol(symident) => sym.join(name) eq IntConstant.constant(symident).toExpression
          }) implies isNegated.fold(symInSyms.not, symInSyms) forAll ((sym oneOf SymbolsRel) and (x oneOf r2))
        }
      } yield (rs2, is2, formula and f2, formula, th2)
    case SetSubEq(e1, e2) =>  evalBinaryBoolExpr(e1, _ in _, e2, th, isNegated)
    case True() => (Set[Relation](), Set[Integer](), Formula.TRUE, Formula.TRUE, th).right
    case And(b1,b2) =>
      for {
        eb1 <- evalBoolExpr(b1, th, isNegated)
        (rs1, is1, fs1, r1, th1) = eb1
        eb2 <- evalBoolExpr(b2, th1, isNegated)
        (rs2, is2, fs2, r2, th2) = eb2
      } yield (rs1 union rs2, is1 union is2,  fs1 and fs2, isNegated.fold(r1 or r2, r1 and r2), th2)
    case Not(b) => for {
        eb <- evalBoolExpr(b, th, !isNegated)
        (rs1, is1, f1, r, th1) = eb
      } yield (rs1, is1, f1, r, th1)
  }

  def evalBinaryBoolExpr(e1: SetExpr[IsSymbolic.type], op: (Expression, Expression) => Formula, e2: SetExpr[IsSymbolic.type],
                         th: Map[Symbols, Relation], isNegated: Boolean): String \/ EvalRes[Formula] = {
    for {
      ee1 <- evalSetExpr(e1, th)
      (rs1, is1, f1, r1, th1) = ee1
      ee2 <- evalSetExpr(e2, th1)
      (rs2, is2, f2, r2, th2) = ee2
      formula = {
        val x1 = Variable.unary("x1")
        val x2 = Variable.unary("x2")
        val res = op(x1.join(syms), x2.join(syms))
        isNegated.fold(res.not, res) forAll ((x1 oneOf r1) and (x2 oneOf r2))
      }
    } yield (rs1 union rs2, is1 union is2, formula and f1 and f2, formula, th2)
  }

  def evalSetExpr(e : SetExpr[IsSymbolic.type], th : Map[Symbols, Relation] = Map()): String \/ EvalRes[Relation] = e match {
    case SetLit(es@_*) =>
      val s = freshSet
      val formula = {
        val ss = Variable.unary("ss")
        if (es.isEmpty) (ss.join(syms) eq Expression.NONE forAll (ss oneOf s))
        else {
          val sym = Variable.unary("sym")
          val ees = es.map {
            case Symbol(ident) => (sym.join(name) eq IntConstant.constant(ident).toExpression)
          }.toList
          val ee1 :: ees1 = ees
          (ss.join(syms) eq (ees1.fold(ee1)(_ or _) comprehension (sym oneOf SymbolsRel))) forAll (ss oneOf s)
        }
      }
      val symbols = es.filter(_.isInstanceOf[Symbol]).map(b => Int.box(b.asInstanceOf[Symbol].id))
      (Set(s), symbols.toSet, formula, s, th).right[String]
    case Union(e1, e2) =>
      evalBinarySetExpr(e1, _ union _, e2, th)
    case Diff(e1, e2) =>
      evalBinarySetExpr(e1, _ difference _, e2, th)
    case ISect(e1, e2) =>
      evalBinarySetExpr(e1, _ intersection _, e2, th)
    case SetSymbol(ident) =>
      if (th.contains(ident)) (Set[Relation](), Set[Integer](), Formula.TRUE, th(ident), th).right[String]
      else {
        val s = freshSet
        val formula = Formula.TRUE
        (Set[Relation](s), Set[Integer](), formula, s, th + (ident -> s)).right[String]
      }
  }

  def evalBinarySetExpr(e1: SetExpr[IsSymbolic.type], op: (Expression, Expression) => Expression, e2: SetExpr[IsSymbolic.type],
                        th : Map[Symbols, Relation]): String \/ EvalRes[Relation] = {
    for {
      ee1 <- evalSetExpr(e1,th)
      (rs1, is1, f1, r1, th1) = ee1
      ee2 <- evalSetExpr(e2,th1)
      (rs2, is2, f2, r2, th2) = ee2
      s = freshSet
      formula = {
        val x = Variable.unary("x")
        val x1 = Variable.unary("x1")
        val x2 = Variable.unary("x2")
        x.join(syms) eq op(x1.join(syms),x2.join(syms)) forAll ((x oneOf s) and (x1 oneOf r1) and (x2 oneOf r2))
      }
    } yield (Set(s) union rs1 union rs2, is1 union is2, formula and f1 and f2, s, th2)
  }

  def relevantConstraints(e: SetExpr[IsSymbolic.type], p: Prop): (Prop, Prop) = {
    val (disj, norm) = p partition {
      case Eq(ISect(_,_), SetLit()) => true
      case _ => false
    }
    def rlv(syms: Set[Symbols], visited: Set[Symbols]): Prop = {
      val relevant = norm.filter((b : BoolExpr[IsSymbolic.type]) => !(b.symbols.ids intersect syms).isEmpty)
      val relevantsyms = relevant.symbols.ids diff visited
      relevant ++ (if (!relevantsyms.isEmpty)
                        rlv(relevantsyms, visited ++ syms)
                  else Set())
    }
    (disj, rlv(e.symbols.ids, Set()))
  }

  def applySubst(th: Map[Symbols, Set[ast.Symbols]], mem: SMem): SMem = {
    mem.subst_all(th.mapValues(s => SetLit[IsSymbolic.type](s.map(Symbol(_)).toSeq :_*))) |>
        (mem => SetNormalizer.normalize(mem.heap.pure)(mem) |> _sm_heap.modify(expand))
  }

  def ownershipConstraints(spatial: Spatial): Prop = {
    spatial.flatMap{ case (sym, sd) => sd match {
      case SpatialDesc(c, typ, children, refs) => children.values.map(e => not(SetMem(Symbol(sym), e)))
    }}.toSet
  }

  def typeConstraints(heap: SHeap) = heap.spatial.map { case (sym, sd) => sd match {
    case SpatialDesc(c, typ, children, refs) => ???
    }
  }

  def findSet(e : SetExpr[IsSymbolic.type], heap: SHeap, minSymbols : Int):
      Process[Task, String \/ (Map[Symbols, Set[ast.Symbols]], Set[ast.Symbols])] = {
    def resolveSetLit(r: Relation, rels: mutable.Map[Relation, TupleSet]): Set[ast.Symbols] = {
      val rval = rels(r).iterator.next.atom(0)
      val rsyms = rels(syms).iterator.asScala.filter(_.atom(0) == rval).map(_.atom(1)).toSet
      val rsymids = rels(name).iterator.asScala.filter(
        t => rsyms.contains(t.atom(0))).map(_.atom(1).asInstanceOf[Integer].intValue)
      rsymids.toSet
    }
    SetNormalizer.normalize(heap.pure)(e) match {
      case lit: SetLit[IsSymbolic.type] =>
        Process((Map[Symbols, Set[ast.Symbols]](), lit.es.map { case Symbol(ident) => ident}.toSet).right[String])
      case _ =>
        logger.debug(s"finding set for ${PrettyPrinter.pretty(e)}...")
        val ee = evalSetExpr(e)
        // TODO: Add spatial derived constraints
        Process(ee).flatMap(t => (for {
            tt <- t
            (rs0, is0, fs0, r, th0) = tt
            //typec = typeConstraints(heap)
            ownershipc = ownershipConstraints(heap.spatial)
            (disj, relv) = relevantConstraints(e, heap.pure ++ ownershipc)
            ps = disj ++ relv
            eps <- ps.foldLeftM[StringE, EvalRes[Formula]]((rs0, is0, fs0, Formula.TRUE, th0)) { (st, b) =>
              val (rs, is, fs, f, th) = st
              for {
                eb <- evalBoolExpr(b, th)
                (rs2, is2, fs2, f2, th2) = eb
              } yield (rs ++ rs2, is ++ is2, fs and fs2, f and f2, th2)
            } // TODO: Filter to only handle relevant constraints, perhaps handling disjointness conditions separately
            (rs, is, fs, fs2, th) = eps
            solver = new Solver()
            _ = {
              val fac = SATFactory.DefaultSAT4J
              solver.options.setFlatten(true)
              solver.options.setSolver(fac)
              solver.options.setSymmetryBreaking(20)
            }
            formula = this.constraints and fs and fs2
            bounds = this.bounds(rs, is, minSymbols)
            res = for {
              sol <- io.iterator(Task(solver.solveAll(formula, bounds).asScala))
              _ = println(sol)
              if util.EnumSet.of(Solution.Outcome.SATISFIABLE, Solution.Outcome.TRIVIALLY_SATISFIABLE) contains sol.outcome
              instance = sol.instance
              rels = instance.relationTuples.asScala
            } yield {
              (th.filterKeys(k => !(disj.symbols.ids diff (relv.symbols.ids union e.symbols.ids)).contains(k)).mapValues(resolveSetLit(_, rels)), resolveSetLit(r, rels))
            }
          } yield res).sequenceU)
    }
  }

  def mkAbstractSpatialDesc(cl : Class): SpatialDesc = {
    val clSupers = defs.supertypes(cl)
    val children = defs.childrenOf(clSupers) mapValues { _ => SetSymbol(symcounter.++) }
    val refs = defs.refsOf(clSupers) mapValues  { _ => SetSymbol(symcounter.++) }
    // TODO: REALLY: Add meta information in setsymbol map
    SpatialDesc(cl, AbstractDesc, children, refs)
  }

  def freshSetSymbol(cl : Class, card : Cardinality) : List[(SetExpr[IsSymbolic.type], Spatial, Set[QSpatial])] = {
    // TODO encode cardinality constraints in KodKod instead
    card match {
      case Single => {
        val sym = symcounter.++
        List((SetLit(Symbol(sym)), Map(sym -> mkAbstractSpatialDesc(cl)), Set[QSpatial]()))
      }
      case Many => {
        val sym = SetSymbol(symcounter.++)
        List((sym, Map[Symbols, SpatialDesc](), Set(QSpatial(sym, cl))))
      }
      case Opt => {
        val sym = symcounter.++
        List((SetLit(Symbol(sym)), Map(sym -> mkAbstractSpatialDesc(cl)), Set[QSpatial]()),
          (SetLit(), Map[Symbols, SpatialDesc](), Set[QSpatial]()))
      }
    }
  }

  def expand(heap: SHeap): SHeap = {
    val (newspatial, newqspatial) = heap.qspatial.foldLeft((heap.spatial, Set[QSpatial]())) {
      (part : (Spatial, Set[QSpatial]), qs : QSpatial) => qs.e match {
          // TODO: Use String \/ - instead
        case SetLit(as @_*) =>
          val expanded: Map[Symbols, SpatialDesc] =
            (as map { case s: Symbol => s } map { _.id -> mkAbstractSpatialDesc(qs.c) }).toMap
          // TODO: Consider a good way to merge things
          (part._1 ++ expanded, part._2)
        case _ => (part._1, part._2 + qs)
      }
    }
    SHeap(newspatial, newqspatial, heap.pure)
  }

  def unfold(sym : Symbols, sd : SpatialDesc, initHeap: SHeap, currentHeap: SHeap): Process0[String \/ (SpatialDesc, SHeap, SHeap)] = {
    def all_children(c : Class) : Map[Fields, (Class, Cardinality)] = {
      val defc = defs(c)
      defc.children ++ defc.superclass.map(all_children).getOrElse(Map())
    }
    def all_references(c : Class) : Map[Fields, (Class, Cardinality)] = {
      val defc = defs(c)
      defc.refs ++ defc.superclass.map(all_references).getOrElse(Map())
    }
    sd match {
      case sd@SpatialDesc(c, ExactDesc, children, refs) => Process((sd, initHeap, currentHeap).right)
      case sd@SpatialDesc(c, AbstractDesc, children, refs) =>
        logger.debug(s"unfolding ${PrettyPrinter.pretty(Map(sym -> sd))}...")
        //TODO Fix this to be partial concretisation instead
        (for {
           defc <- Process(defs.get(c).cata(_.right, s"Class definition of $c is unknown".left)).interleaved
           // Type inference is a bit limited for higher-kinded types
           sts <- defc.traverse(dc => Process((defs.subtypesOrSelf(Class(dc.name)))
                      .toList.filter(_ != Class("Nothing")) : _*))(pmn).interleaved
           cdc <- sts.traverse[Process0, String, (SpatialDesc, SHeap, SHeap)](st => for {
                     cs <- Process(all_children(st).mapValues(v => freshSetSymbol(v._1, v._2)).sequenceU :_*)
                     rs  <- Process(all_references(st).mapValues(v => freshSetSymbol(v._1, v._2)).sequenceU :_*)
                     chlds = cs.mapValues(_._1)
                     refs  = rs.mapValues(_._1)
                     all = cs.values.toList ++ rs.values.toList
                     (_, newspatials, newqspatials) = all.unzip3(identity)
                     newspatial = newspatials.foldLeft(Map[Symbols, SpatialDesc]())(_ ++ _)
                     newqspatial = newqspatials.foldLeft(Set[QSpatial]())(_ ++ _)
                     cd =  SpatialDesc(st, ExactDesc, chlds, refs)
                     upd = _sh_spatial.modify(_.updated(sym, cd) ++ newspatial) `andThen` _sh_qspatial.modify(_ ++ newqspatial)
                   } yield (cd, if (initHeap.spatial.contains(sym)) upd(initHeap) else initHeap, upd(currentHeap)))(pmn).interleaved
        } yield cdc).toProcess
      case _ => ??? // TODO: REALLY: Implement this for partial descs
    }
  }

  def unfold_all(syms : Set[Symbols], initHeap: SHeap, currentHeap: SHeap): Process0[String \/ (SHeap, SHeap)] = {
    syms.toList.foldLeft[Process0[String \/ (SHeap, SHeap)]](Process((initHeap, currentHeap).right))((heaps: Process0[String \/ (SHeap, SHeap)], sym : Symbols) =>
      for {
        he <- heaps
        newheaps <-  he.flatMap { case (ih, ch) => for {
           symv <- ch.spatial.get(sym).cata(_.right, s"Unknown symbol: ${PrettyPrinter.pretty(Symbol(sym))}".left)
           newheaps = unfold(sym, symv, ih, ch)
        } yield newheaps }.traverse(identity)(pmn).map(_.join.map { case (_, ih, ch) => (ih, ch) })
      } yield newheaps)
  }

  def concretise(el: Set[Symbols], initialMem: SMem, currentMem: SMem, alsoReferences: Boolean = false, depth: Int = delta, c: Option[Class] = None): Process[Task, String \/ (SMem, SMem)] = {
    def typeFilter(c1: Class) = c.cata(c2 => defs.canContain(c1, c2), true)
    def concretise_final(el: Set[Symbols], initialMem: SMem, currentMem: SMem): Process[Task, String \/ (SMem, SMem)] = {
      el.foldLeft(Process((initialMem, currentMem).right) : Process[Task, String \/ (SMem, SMem)]) { (memr: Process[Task, String \/ (SMem, SMem)], sym: Symbols) =>
        for {
          mem <- memr
          res <- mem.traverse[TProcess, String, String \/ (SMem, SMem)]({ case (initMem, curMem) => for {
              symv <- Process(curMem.heap.spatial.get(sym).toSeq :_*)
              cd <- symv.typ liftMatch[SpatialDesc, ({ type l[A] = Process[Task, A]})#l] { case ExactDesc => symv }
              defc <- Process(defs.get(cd.c).toSeq : _*)
              thr <- if (defc.children.values.forall(_._2.isOptional)
                          && (if (alsoReferences) defc.refs.values.forall(_._2.isOptional) else true)) {
                            val childExprs = symv.children.values.toSet
                            val refExprs = symv.refs.values.toSet
                            val allExprs = childExprs ++ (if (alsoReferences) refExprs else Set())
                            val finalConstraints = allExprs.map(Eq(_, SetLit()))
                            findSet(allExprs.foldLeft(SetLit() : SetExpr[IsSymbolic.type])(Union(_,_)),
                                _sh_pure.modify(_ ++ finalConstraints)(curMem.heap), beta).map(_.map(_._1))
                         } else Process()
              res = thr.map { th =>
                  (applySubst(th, initMem), applySubst(th, initMem))
              }
          } yield res })(pmt).map(_.join)
          /*_sh_spatial.modify(_.updated(sym, _cd_children.modify(_.mapValues(v => SetLit()))(cd)))(hh)*/
        } yield res
      }
    }
    // TODO Convert all SetLit to expression
    def concretise_helper(el: Set[ast.Symbols], initialMem: SMem, currentMem: SMem, depth: Int): Process[Task, String \/ (SMem, SMem)] = {
      logger.debug(s"concretising ${PrettyPrinter.pretty(SetLit(el.toSeq.map(Symbol(_)):_*))} at depth $depth}...")
      if (depth <= 0 || el.isEmpty) {
        concretise_final(el, initialMem, currentMem)
      }
      else for {
        unfolded <- unfold_all(el, initialMem.heap, currentMem.heap)
        res <- unfolded.traverse[TProcess, String, String \/ (SMem, SMem)]{ case (ih, ch) => {
          // TODO handle safely
          val childes = el.toList.flatMap(_.|>(ch.spatial.get)
              .flatMap(_ liftMatch[SpatialDesc, Option] { case sd@SpatialDesc(_, ExactDesc, _, _) => sd })
              .map(cd => if (typeFilter(cd.c)) cd.children.values else Set()).get)
          val refes = el.toList.flatMap(_.|>(ch.spatial.get)
              .flatMap(_ liftMatch[SpatialDesc, Option] { case sd@SpatialDesc(_, ExactDesc, _, _) => sd })
              .map(cd => if(typeFilter(cd.c)) cd.refs.values else Set()).get)
          val alles = childes ++ (if (alsoReferences) refes else Set())
          val (newInitialMem, newCurrentMem) = (_sm_heap.set(ih)(initialMem), _sm_heap.set(ch)(currentMem))
          // TODO, we may actually need to iterate each child individually to not restrict the shapes
          // Just join everything together
          // val joinede = allSyms.foldLeft(SetLit() : SetExpr)(Union)
          // blackHole(childes)
          alles.foldLeft[TProcess[String \/ (SMem, SMem)]](Process((newInitialMem, newCurrentMem).right)) { (pmemr, e) =>
            pmemr.interleaved.flatMap {
              memr => memr.traverse[TProcess, String, String \/ (SMem, SMem)] { case (nim, ncm) =>
                (for {
                  pth <- findSet(e, ch, beta).interleaved
                  memr = pth.map { case (th, els) =>
                    (applySubst(th, nim), applySubst(th, ncm), els)
                  }
                  cfinal = memr.traverse[TProcess,String, String \/ (SMem, SMem)]{
                      case (nim:SMem, ncm:SMem, els : Set[Symbols]) => concretise_final(el, nim, ncm)
                  }.map(_.join)
                  cfurther = memr.traverse[TProcess, String, String \/ (SMem, SMem)]{
                    case (nim:SMem, ncm:SMem, els : Set[Symbols]) => concretise_helper(els, nim, ncm, depth - 1)
                  }.map(_.join)
                  concretised <- cfinal.tee(cfurther)(teePlus.interleaveAll).interleaved
                } yield concretised).toProcess
              }(pmt).map(_.join).interleaved
            }.toProcess
          }
        }}(pmt).map(_.join)
      } yield res
    }
    concretise_helper(el, initialMem, currentMem, depth)
  }

}
