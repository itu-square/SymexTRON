package syntax

import helper._
import scalaz._, Scalaz._

package object ast extends SymbolicOps {
  type Vars = String
  type Symbols = Int
  type Fields = String
  type Spatial[T] = Map[T, SpatialDesc]
  type Prop = Set[BoolExpr[IsSymbolic]]
  type SStack = Map[Vars, SetExpr[IsSymbolic]]
  type Instances = Int
  type CStack = Map[Vars, Set[Instances]]
  type IsSymbolic = IsSymbolic.type
  type IsProgram  = IsProgram.type

  def not[T <: ASTType](p : BoolExpr[T]) : BoolExpr[T] = p match {
    case Not(Not(p)) => not(p)
    case Not(p) => p
    case p => Not(p)
  } //Smart constructor

  def or[T <: ASTType](p1 : BoolExpr[T], p2 : BoolExpr[T]): BoolExpr[T] = Not(And(Not(p1), Not(p2)))

  def getSingletonSymbolId(e : SetExpr[IsSymbolic]): String \/ Symbols = {
    e match {
      case SetLit(Symbol(sym)) => sym.right
      case _ => s"${PrettyPrinter.pretty(e)} is not a single symbol".left
    }
  }

  implicit class RichDefs(defs: Map[Class, ClassDefinition]){
    val childfields: Set[Fields] = defs.values.flatMap(_.children.keys).toSet
    val reffields: Set[Fields]   = defs.values.flatMap(_.refs.keys).toSet

    // Consolidate supertypes and subtypes fields

    def fieldType(c : Class, f : Fields): Option[(Class, Cardinality)] =
      (Set(c) ++ supertypes(c)).map(defs).find(cdef =>
        cdef.children.contains(f) || cdef.refs.contains(f)
      ).flatMap(cdef => cdef.children.get(f)
                            .orElse(cdef.refs.get(f)))

    def supertypes(c : Class): Set[Class] =
     (if (c == Class("Nothing")) defs.keys.toSet
     else defs(c).superclass.toSet.|>(s =>
      s ++ s.flatMap(supertypes _)
    )) + Class("Any")

    val subtypes: Map[Class, Set[Class]] = defs.mapValues(_ => Set[Class]()) ++ {
      defs.values.foldLeft(Map[Class, Set[Class]]())((m : Map[Class, Set[Class]], cd: ClassDefinition) =>
        cd.superclass.cata(sup => m.adjust(sup)(_ + Class(cd.name) + Class("Nothing")), m)
      ).trans
    } + (Class("Any") -> defs.keys.toSet)

    val subtypesOrSelf: Map[Class, Set[Class]] =
      subtypes.map(((c : Class, sts : Set[Class]) => (c, sts + c)).tupled)


    val containing: Map[Class, Set[Class]] = defs.values.foldLeft[Map[Class, Set[Class]]](Map()) {(m, cd) =>
      val c = Class(cd.name)
      val sts = subtypesOrSelf
      val childfieldtypes = (Set(c) ++ supertypes(c))
                                .map(defs)
                                .flatMap(_.children.values.map(_._1).toSet)
                                .flatMap(sts)
      m + (c -> childfieldtypes)
    }.trans ++ Map[Class, Set[Class]](Class("Any") -> Set(), Class("Nothing") -> Set())

    def canContain(c1 : Class, c2 : Class): Boolean = {
      val cts = containing
      val supertypesOrSelf = (Set(c2) ++ defs.supertypes(c2))
      supertypesOrSelf.exists(ct => cts(c1).contains(ct))
    }

    {
      val commoncr = childfields intersect reffields
      assert(commoncr.isEmpty, s"There are overlapping names used for fields and references: ${commoncr.mkString(", ")}")
    }
  }
}
