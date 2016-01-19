package syntax.ast

import scalaz._, Scalaz._

trait Symbolic {
  val symbols: Set[SetSymbol \/ Symbol]
}

trait SymbolicOps {
  implicit class SymbolicSetExpr(e: SetExpr[IsSymbolic.type]) extends Symbolic {
    override val symbols = {
      def symbols(e: SetExpr[IsSymbolic.type]): Set[SetSymbol \/ Symbol] = e match {
        case SetLit(es@_*) => es.collect{ case x: Symbol => x.right }.toSet
        case Union(e1, e2) => symbols(e1) ++ symbols(e2)
        case Diff(e1, e2) => symbols(e1) ++ symbols(e2)
        case ISect(e1, e2) => symbols(e1) ++ symbols(e2)
        case e@SetSymbol(c, id) => Set(e.left)
      }
      symbols(e)
    }
  }

  implicit class SymbolicBoolExpr(b : BoolExpr[IsSymbolic.type]) extends Symbolic {
    override val symbols = {
      def symbols(b: BoolExpr[IsSymbolic.type]): Set[SetSymbol \/ Symbol] = b match {
        case Eq(e1, e2) => e1.symbols ++ e2.symbols
        case SetMem(e1, e2) => SetLit(e1).symbols ++ e2.symbols
        case SetSubEq(e1, e2) => e1.symbols ++ e2.symbols
        case True() => Set()
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
      case SpatialDesc(_, _, children, refs) =>
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

  implicit class SymbolicSStack(stack : SStack) extends Symbolic {
    override val symbols = stack.values.toSet.flatMap((e : SetExpr[IsSymbolic.type]) => e.symbols)
  }

  implicit class SymbolicSMem(mem : SMem) extends Symbolic {
    override val symbols = mem.stack.symbols ++ mem.heap.symbols
  }

  implicit class SymbolIds(s : Set[SetSymbol \/ Symbol]) {
    val ids = s.map(_.fold(_.id,_.id))
  }
}
