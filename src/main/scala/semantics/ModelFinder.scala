package semantics

import java.util

import scala.language.reflectiveCalls

import helper.Ref
import kodkod.ast._
import kodkod.engine.satlab.SATFactory
import kodkod.engine.{Solution, Solver}
import kodkod.instance.{Bounds, TupleSet, Universe}
import syntax.ast._

import scala.collection.JavaConverters._
import scala.collection.mutable
import scalaz.\/._
import scalaz._, Scalaz._

class ModelFinder(symcounter : Ref[Int], defs: Map[Class, ClassDefinition] = Map()) {
  private type EvalRes =  (Set[Relation], Set[Integer], Formula, Relation, Map[Symbols, Relation])

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

  def evalSetExpr(e : SetExpr, th : Map[Symbols, Relation] = Map()): String \/ EvalRes = e match {
    case SetLit(es@_*) =>
      val s = freshSet
      val formula = {
        val ss = Variable.unary("ss")
        if (es.isEmpty) right(ss.join(syms) eq Expression.NONE forAll (ss oneOf s))
        else {
          val sym = Variable.unary("sym")
          val ees:  String \/ List[Formula] = es.map {
            case Symbol(id) => right(sym.join(name) eq IntConstant.constant(id).toExpression)
            case Var(x) => left(s"Error: unevaluated variable: $name")
          }.toList.sequence[({ type S[a] = String \/ a })#S, Formula]
          ees.fold(left, ees => right {
            val ee1 :: ees1 = ees
            (ss.join(syms) eq (ees1.fold(ee1)(_ or _) comprehension (sym oneOf Symbols))) forAll (ss oneOf s)
          })
        }
      }
      formula.fold(left, formula => right {
        val symbols = es.filter(_.isInstanceOf[Symbol]).map(b => Int.box(b.asInstanceOf[Symbol].id))
        (Set(s), symbols.toSet, formula, s, Map())
      })

    case Union(e1, e2) =>
      evalBinarySetExpr(e1, _ union _, e2, th)
    case Diff(e1, e2) =>
      evalBinarySetExpr(e1, _ difference _, e2, th)
    case ISect(e1, e2) =>
      evalBinarySetExpr(e1, _ intersection _, e2, th)
    case Match(e, s) => ???
    case MatchStar(e, s) => ???
    case SetSymbol(id) =>
      if (th.contains(id)) right[String, EvalRes](Set(), Set(), Formula.TRUE, th(id), th)
      else {
        val s = freshSet
        right[String, EvalRes](Set(s), Set(), Formula.TRUE, s, th + (id -> s))
      }
    case SetVar(nm) => left(s"Error: unevaluated variable: $nm")
  }

  def evalBinarySetExpr(e1: SetExpr, op: (Expression, Expression) => Expression, e2: SetExpr,
                        th : Map[Symbols, Relation]): String \/ EvalRes = {
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
        x.join(syms).eq(op(x1.join(syms),x2.join(syms))) forAll ((x oneOf s) and (x1 oneOf r1) and (x2 oneOf r2))
      }
    } yield (Set(s) union rs1 union rs2, is1 union is2, formula and f1 and f2, s, th2)
  }

  def findSet(e : SetExpr, minSymbols : Int = 5): String \/ Iterator[(Map[Symbols, SetLit], SetLit)] = {
    def resolveSetLit(r: Relation, rels: mutable.Map[Relation, TupleSet]): SetLit = {
      val rval = rels(r).iterator.next.atom(0)
      val rsyms = rels(syms).iterator.asScala.filter(_.atom(0) == rval).map(_.atom(1)).toSet
      val rsymids = rels(name).iterator.asScala.filter(
        t => rsyms.contains(t.atom(0))).map(_.atom(1).asInstanceOf[Integer].intValue)
      SetLit(rsymids.toList.map(Symbol): _*)
    }
    e match {
      case lit: SetLit => right(Set((Map[Symbols, SetLit](), lit)).iterator)
      case _ =>
        val solver = new Solver()
        val ee = evalSetExpr(e)
        ee.fold[String \/ Iterator[(Map[Symbols, SetLit], SetLit)]](left, { t => right
          {
            val (rs, is, fs, r, th) = t
            solver.options.setSolver(SATFactory.DefaultSAT4J)
            solver.options.setSymmetryBreaking(20)
            for {
              sol <- solver.solveAll(this.constraints and fs, this.bounds(rs, is, minSymbols)).asScala
              if util.EnumSet.of(Solution.Outcome.SATISFIABLE, Solution.Outcome.TRIVIALLY_SATISFIABLE) contains sol.outcome
              instance = sol.instance
              rels = instance.relationTuples.asScala
            } yield {
              (th.mapValues(resolveSetLit(_, rels)), resolveSetLit(r, rels))
            }
          }})
    }
  }

}

/* Sudoku example

class Sudoku {
  val number = Relation.unary("Number")
  val data = Relation.ternary("data")
  val regions = for (i <- 1 to 3) yield Relation.unary(s"Region$i")

  def complete(rows : Expression, cols : Expression): Formula =
    number in (cols join (rows join data))

  def rules: Formula = {
    val f1 = {
      val x = Variable.unary("x")
      val y = Variable.unary("y")
      y.join(x.join(data)).lone forAll ((x oneOf number) and (y oneOf number))
    }

    val f2 = {
      val row = Variable.unary("row")
      complete(row, number) forAll (row oneOf number)
    }

    val f3 = {
      val col = Variable.unary("col")
      complete(col, number) forAll (col oneOf number)
    }

    (for (rx <- regions; ry <- regions)
      yield complete(rx, ry)).fold(f1 and f2 and f3)(_ and _)
  }

  def puzzle: Bounds = {
    val atoms = (for (i <- 1 to 9) yield Int.box(i)).toSet
    val u = new Universe(atoms.asJava)
    val b = new Bounds(u)
    val f = u.factory

    b.boundExactly(number, f allOf 1)
    b.boundExactly(regions(0), f setOf (List[Integer](1, 2, 3) :_*))
    b.boundExactly(regions(1), f setOf (List[Integer](4, 5, 6) :_*))
    b.boundExactly(regions(2), f setOf (List[Integer](7, 8, 9) :_*))

    val givens = f noneOf 3
    givens.add(f tuple (List[Integer](1, 1, 1) :_*)); givens.add(f tuple (List[Integer](1, 4, 2) :_*)); givens.add(f tuple (List[Integer](1, 7, 3) :_*))
    givens.add(f tuple (List[Integer](2, 2, 2) :_*)); givens.add(f tuple (List[Integer](2, 5, 3) :_*)); givens.add(f tuple (List[Integer](2, 8, 4) :_*))
    givens.add(f tuple (List[Integer](3, 3, 3) :_*)); givens.add(f tuple (List[Integer](3, 6, 4) :_*)); givens.add(f tuple (List[Integer](3, 9, 5) :_*))
    givens.add(f tuple (List[Integer](4, 1, 6) :_*)); givens.add(f tuple (List[Integer](4, 4, 4) :_*)); givens.add(f tuple (List[Integer](4, 7, 5) :_*))
    givens.add(f tuple (List[Integer](5, 2, 7) :_*)); givens.add(f tuple (List[Integer](5, 5, 5) :_*)); givens.add(f tuple (List[Integer](5, 8, 6) :_*))
    givens.add(f tuple (List[Integer](6, 3, 8) :_*)); givens.add(f tuple (List[Integer](6, 6, 6) :_*)); givens.add(f tuple (List[Integer](6, 9, 7) :_*))
    givens.add(f tuple (List[Integer](7, 1, 8) :_*)); givens.add(f tuple (List[Integer](7, 4, 9) :_*)); givens.add(f tuple (List[Integer](7, 7, 7) :_*))
    givens.add(f tuple (List[Integer](8, 2, 9) :_*)); givens.add(f tuple (List[Integer](8, 5, 1) :_*)); givens.add(f tuple (List[Integer](8, 8, 8) :_*))
    givens.add(f tuple (List[Integer](9, 3, 1) :_*)); givens.add(f tuple (List[Integer](9, 6, 2) :_*)); givens.add(f tuple (List[Integer](9, 9, 4) :_*))

    b.bound(data, givens, f allOf 3)

    b
  }

}

object Sudoku {
  def main(args: Array[String]) {
    val solver = new Solver()
    solver.options.setSolver(SATFactory.DefaultSAT4J)
    solver.options.setSymmetryBreaking(20)
    solver.options.setSkolemDepth(3)
    val sudoku = new Sudoku()
    for (sol <- solver.solveAll(sudoku.rules, sudoku.puzzle).asScala)
      println(sol)
  }
}*/
