package semantics

import kodkod.ast._
import kodkod.engine.Solver
import kodkod.engine.satlab.SATFactory
import kodkod.instance.{Bounds, Universe}
import scala.collection.JavaConverters._

class ModelFinder {

}

// Sudoku example

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
    val sudoku = new Sudoku()
    for (sol <- solver.solveAll(sudoku.rules, sudoku.puzzle).asScala)
      println(sol)
  }
}
