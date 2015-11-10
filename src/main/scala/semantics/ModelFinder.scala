package semantics

import java.util

import kodkod.ast._
import kodkod.engine.satlab.SATFactory
import kodkod.engine.{Solution, Solver}
import kodkod.instance.{Bounds, TupleSet, Universe}

import syntax.ast._
import helper._

import scala.collection.JavaConverters._
import scala.collection.mutable
import scalaz._, Scalaz._
import scalaz.concurrent.Task
import scalaz.stream._



class ModelFinder(symcounter : Counter, defs: Map[Class, ClassDefinition] = Map()) {
  private type StringE[T] = String \/ T
  private type EvalRes[T] = (Set[Relation], Set[Integer], Formula, T, Map[Symbols, Relation])

  var counter = 0

  val SymbolicSet = Relation.unary("SymbolicSet")
  val syms = Relation.binary("syms")


  val Symbols = Relation.unary("Symbols")
  val name = Relation.binary("name")

  def freshSet : Relation = {
    counter = counter + 1
    Relation.unary(s"ConcreteSymbolicSet$counter")
  }

  def constraints : Formula = {
    val nameTyping = {
      val s = Variable.unary("s")
      (s.join(name).one and (s.join(name) in Expression.INTS) forAll (s oneOf Symbols)) and
        (name.join(Expression.UNIV) in Symbols)
    }
    val symsTyping = {
      val ss = Variable.unary("ss")
      ((ss.join(syms) in Symbols) forAll (ss oneOf SymbolicSet)) and
        (syms.join(Expression.UNIV) in SymbolicSet)
    }
    val nameUniqueness = {
      val s1 = Variable.unary("s1")
      val s2 = Variable.unary("s2")
      (s1 eq s2) iff (s1.join(name) eq s2.join(name)) forAll ((s1 oneOf Symbols) and (s2 oneOf Symbols))
    }
    nameTyping and nameUniqueness and symsTyping
  }


  def bounds(rs : Set[Relation], is : Set[Integer], minSymbols : Int) : Bounds = {
    val symbolintnames = (for (i <- 1 to (minSymbols - is.size)) yield {
      symcounter := !symcounter + 1
      Int.box(!symcounter)
    }).toSet ++ is

    val symbolids = symbolintnames.toList.sorted.map(i => s"sym'$i")
    val symbolicsets = for ((r, i) <- rs.zipWithIndex) yield (r, s"set'$i")
    val atoms =  symbolintnames ++ symbolids ++ symbolicsets.map(_._2)
    val universe = new Universe(atoms.asJava)
    val bounds = new Bounds(universe)
    val f = universe.factory

    bounds.boundExactly(Symbols, f setOf (symbolids :_*))
    for ((r, i) <- symbolicsets) bounds.boundExactly(r, f setOf i)
    bounds.boundExactly(SymbolicSet, f setOf (symbolicsets.map(_._2).toSeq :_*))

    for (symname <- symbolintnames)
      bounds.boundExactly(symname.intValue, f range (f tuple symname, f tuple symname))

    bounds.bound(syms, f allOf 2)
    val nameUpper = f noneOf 2
    for ((sid, sname) <- symbolids.zip(symbolintnames.toList.sorted))
      nameUpper.add((f tuple sid) product (f tuple sname))
    bounds.bound(name, nameUpper)
    bounds
  }

  def evalBoolExpr(b : BoolExpr, th : Map[Symbols, Relation])
  : String \/ EvalRes[Formula] = b match {
    case Eq(e1, e2) => evalBinaryBoolExpr(e1, _ eq _, e2, th)
    case ClassMem(e1, s) => ???
    case SetMem(e1, e2) => for {
        _ <- e1 match {
          case Var(name) => s"Error: unevaluated variable: $name".left
          case _ => ().right
        }
        ee2 <- evalSetExpr(e2, th)
        (rs2, is2, f2, r2, th2) = ee2
        formula = {
          val sym = Variable.unary("sym")
          val x = Variable.unary("x")
          (e1 match {
            case Symbol(symident) => sym.join(name) eq IntConstant.constant(symident).toExpression
            case Var(name) => impossible
          }) implies (sym in x.join(syms)) forAll ((sym oneOf Symbols) and (x oneOf r2))
        }
      } yield (rs2, is2, formula and f2, formula, th2)
    case SetSubEq(e1, e2) =>  evalBinaryBoolExpr(e1, _ in _, e2, th)
    case True => (Set[Relation](), Set[Integer](), Formula.TRUE, Formula.TRUE, th).right
    case And(b1,b2) =>
      for {
        eb1 <- evalBoolExpr(b1, th)
        (rs1, is1, fs1, r1, th1) = eb1
        eb2 <- evalBoolExpr(b2, th1)
        (rs2, is2, fs2, r2, th2) = eb2
      } yield (rs1 union rs2, is1 union is2, fs1 and fs2, r1 and r2, th2)
    case Not(b) => for {
        eb <- evalBoolExpr(b, th)
        (rs1, is1, f1, r, th1) = eb
      } yield (rs1, is1, f1, r.not, th1)
  }

  def evalBinaryBoolExpr(e1: SetExpr, op: (Expression, Expression) => Formula, e2: SetExpr,
                         th: Map[Symbols, Relation]): String \/ EvalRes[Formula] = {
    for {
      ee1 <- evalSetExpr(e1, th)
      (rs1, is1, f1, r1, th1) = ee1
      ee2 <- evalSetExpr(e2, th1)
      (rs2, is2, f2, r2, th2) = ee2
      formula = {
        val x1 = Variable.unary("x1")
        val x2 = Variable.unary("x2")
        op(x1.join(syms), x2.join(syms)) forAll ((x1 oneOf r1) and (x2 oneOf r2))
      }
    } yield (rs1 union rs2, is1 union is2, formula and f1 and f2, formula, th2)
  }

  def evalSetExpr(e : SetExpr, th : Map[Symbols, Relation] = Map()): String \/ EvalRes[Relation] = e match {
    case SetLit(es@_*) =>
      val s = freshSet
      val formula = {
        val ss = Variable.unary("ss")
        if (es.isEmpty) (ss.join(syms) eq Expression.NONE forAll (ss oneOf s)).right
        else {
          val sym = Variable.unary("sym")
          val ees:  String \/ List[Formula] = es.map {
            case Symbol(ident) => (sym.join(name) eq IntConstant.constant(ident).toExpression).right
            case Var(x) => (s"Error: unevaluated variable: $name").left
          }.toList.sequence[StringE, Formula]
          ees.fold(_.left, ees => {
            val ee1 :: ees1 = ees
            (ss.join(syms) eq (ees1.fold(ee1)(_ or _) comprehension (sym oneOf Symbols))) forAll (ss oneOf s)
          }.right)
        }
      }
      formula.fold[String \/ EvalRes[Relation]](_.left, formula => {
        val symbols = es.filter(_.isInstanceOf[Symbol]).map(b => Int.box(b.asInstanceOf[Symbol].id))
        (Set(s), symbols.toSet, formula, s, th)
      }.right)

    case Union(e1, e2) =>
      evalBinarySetExpr(e1, _ union _, e2, th)
    case Diff(e1, e2) =>
      evalBinarySetExpr(e1, _ difference _, e2, th)
    case ISect(e1, e2) =>
      evalBinarySetExpr(e1, _ intersection _, e2, th)
    case SetSymbol((cl, crd), ident) =>
      if (th.contains(ident)) (Set[Relation](), Set[Integer](), Formula.TRUE, th(ident), th).right[String]
      else {
        val s = freshSet
        val formula = crd match {
          case Many => Formula.TRUE
          case Opt => {
            val ss = Variable.unary("ss")
            (ss.join(syms).count lte IntConstant.constant(1)) forAll (ss oneOf s)
          }
          case Single => {
            val ss = Variable.unary("ss")
            (ss.join(syms).count eq IntConstant.constant(1)) forAll (ss oneOf s)
          }
        }
        (Set[Relation](s), Set[Integer](), formula, s, th + (ident -> s)).right[String]
      }
    case SetVar(nm) => s"Error: unevaluated variable: $nm".left
  }

  def evalBinarySetExpr(e1: SetExpr, op: (Expression, Expression) => Expression, e2: SetExpr,
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

  def findSet(e : SetExpr, heap: SHeap, minSymbols : Int): Process[Task, String \/ (Map[Symbols, SetLit], SetLit)] = {
    def resolveSetLit(r: Relation, rels: mutable.Map[Relation, TupleSet]): SetLit = {
      val rval = rels(r).iterator.next.atom(0)
      val rsyms = rels(syms).iterator.asScala.filter(_.atom(0) == rval).map(_.atom(1)).toSet
      val rsymids = rels(name).iterator.asScala.filter(
        t => rsyms.contains(t.atom(0))).map(_.atom(1).asInstanceOf[Integer].intValue)
      SetLit(rsymids.toList.map(Symbol): _*)
    }
    e match {
      case lit: SetLit => Process((Map[Symbols, SetLit](), lit).right[String])
      case _ =>
        val solver = new Solver()
        val ee = evalSetExpr(e)
        // TODO: Add spatial derived constraints
        Process(ee).flatMap(t => (for {
            tt <- t
            (rs0, is0, fs0, r, th0) = tt
            ps <- heap.pure.foldLeftM[StringE, EvalRes[Formula]]((rs0, is0, fs0, Formula.TRUE, th0)) { (st, b) =>
              val (rs, is, fs, f, th) = st
              for {
                eb <- evalBoolExpr(b, th)
                (rs2, is2, fs2, f2, th2) = eb
              } yield (rs ++ rs2, is ++ is2, fs and fs2, f and f2, th2)
            } // TODO: Filter to only handle relevant constraints, perhaps handling disjointness conditions separately
            (rs, is, fs, fs2, th) = ps
            _ = solver.options.setSolver(SATFactory.DefaultSAT4J)
            _ = solver.options.setSymmetryBreaking(20)
            formula = this.constraints and fs and fs2
            bounds = this.bounds(rs, is, minSymbols)
            res = for {
              sol <- io.iterator(Task(solver.solveAll(formula, bounds).asScala))
              if util.EnumSet.of(Solution.Outcome.SATISFIABLE, Solution.Outcome.TRIVIALLY_SATISFIABLE) contains sol.outcome
              instance = sol.instance
              rels = instance.relationTuples.asScala
            } yield {
              (th.mapValues(resolveSetLit(_, rels)), resolveSetLit(r, rels))
            }
          } yield res).sequenceU)
    }
  }

}
