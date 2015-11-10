package syntax

import helper._
import scalaz._, Scalaz._

package object ast {
  type Vars = String
  type Symbols = Int
  type Fields = String
  type Spatial[T] = Map[T, SpatialDesc]
  type Prop = Set[BoolExpr]
  type SStack = Map[Vars, SetExpr]
  type Instances = Int
  type CStack = Map[Vars, Set[Instances]]

  def not(p : BoolExpr) : BoolExpr = p match {
    case Not(Not(p)) => not(p)
    case Not(p) => p
    case p => Not(p)
  } //Smart constructor

  implicit class RichDefs(defs: Map[Class, ClassDefinition]){
    val childfields: Set[Fields] = defs.values.flatMap(_.children.keys).toSet
    val reffields: Set[Fields]   = defs.values.flatMap(_.refs.keys).toSet

    def fieldType(c : Class, f : Fields): Option[(Class, Cardinality)] =
      (Set(c) ++ supertypes(c)).map(defs).find(cdef =>
        cdef.children.contains(f) || cdef.refs.contains(f)
      ).flatMap(cdef => cdef.children.get(f)
                            .orElse(cdef.refs.get(f)))

    def supertypes(c : Class): Set[Class] = defs(c).supers.toSet.|>(s =>
      s ++ s.flatMap(supertypes _)
    )

    val subtypes: Map[Class, Set[Class]] = defs.mapValues(_ => Set[Class]()) ++ {
      defs.values.foldLeft(Map[Class, Set[Class]]())((m : Map[Class, Set[Class]], cd: ClassDefinition) =>
        cd.supers.foldLeft(m)((m_ : Map[Class, Set[Class]], sup : Class) => m_.adjust(sup)(_ + Class(cd.name)))
      ).trans
    }

    val subtypesOrSelf: Map[Class, Set[Class]] =
      subtypes.map(((c : Class, sts : Set[Class]) => (c, sts + c)).tupled)

    {
      val commoncr = childfields intersect reffields
      assert(commoncr.isEmpty, s"There are overlapping names used for fields and references: ${commoncr.mkString(", ")}")
    }
  }

  implicit class RichSetExpr(e: SetExpr) {
    val symbols = {
      def symbols(e: SetExpr): Set[Symbols] = e match {
        case SetLit(es@_*) => es.collect{ case x: Symbol => x }.map(_.id).toSet
        case Union(e1, e2) => symbols(e1) ++ symbols(e2)
        case Diff(e1, e2) => symbols(e1) ++ symbols(e2)
        case ISect(e1, e2) => symbols(e1) ++ symbols(e2)
        case SetVar(name) => Set()
        case SetSymbol(c, id) => Set(id)
      }
      symbols(e)
    }
  }

  implicit class RichBoolExpr(b : BoolExpr) {
    val symbols = {
      def symbols(b: BoolExpr): Set[Symbols] = b match {
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
}
