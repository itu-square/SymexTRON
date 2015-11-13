package syntax.ast

import scalaz._, Scalaz._

trait Symbolic {
  val symbols: Set[SetSymbol \/ Symbol]
}

trait SymbolicOps {
  implicit class SymbolicSetExpr(e: SetExpr) extends Symbolic {
    override val symbols = {
      def symbols(e: SetExpr): Set[SetSymbol \/ Symbol] = e match {
        case SetLit(es@_*) => es.collect{ case x: Symbol => x.right }.toSet
        case Union(e1, e2) => symbols(e1) ++ symbols(e2)
        case Diff(e1, e2) => symbols(e1) ++ symbols(e2)
        case ISect(e1, e2) => symbols(e1) ++ symbols(e2)
        case SetVar(name) => Set()
        case e@SetSymbol(c, id) => Set(e.left)
      }
      symbols(e)
    }
  }

  implicit class SymbolicBoolExpr(b : BoolExpr) extends Symbolic {
    override val symbols = {
      def symbols(b: BoolExpr): Set[SetSymbol \/ Symbol] = b match {
        case Eq(e1, e2) => e1.symbols ++ e2.symbols
        case ClassMem(e1, s) => e1.symbols
        case SetMem(e1, e2) => SetLit(e1).symbols ++ e2.symbols
        case SetSubEq(e1, e2) => e1.symbols ++ e2.symbols
        case True => Set()
        case And(p1, p2) => symbols(p1) ++ symbols(p2)
        case Not(pp) => symbols(pp)
      }
      symbols(b)
    }
  }

  implicit class SymbolicProp(p : Prop)  extends Symbolic {
    override val symbols = p.map(_.symbols).fold(Set())(_++_)
  }

  implicit class SymbolicSpatialDesc(sd : SpatialDesc) extends Symbolic {
    override val symbols: Set[SetSymbol \/ Symbol] = sd match {
      case AbstractDesc(c) => Set()
      case ConcreteDesc(c, children, refs) =>
        children.values.flatMap(_.symbols).toSet ++
           refs.values.flatMap(_.symbols).toSet
    }
  }

  implicit class SymbolicSpatial(sp : Spatial[Symbols]) extends Symbolic {
    override val symbols = sp.flatMap { case (s, sd) =>
          sd.symbols ++ Set(Symbol(s).right[SetSymbol]) }.toSet
  }

  implicit class SymbolicQSpatial(qsps : Set[QSpatial]) extends Symbolic {
    override val symbols = qsps.flatMap(_.e.symbols).toSet
  }

  implicit class SymbolicSHeap(heap : SHeap) extends Symbolic {
    override val symbols = heap.spatial.symbols ++ heap.qspatial.symbols ++
                            heap.pure.symbols
  }

  implicit class SymbolIds(s : Set[SetSymbol \/ Symbol]) {
    val ids = s.map(_.fold(_.id,_.id))
  }
}
