package examples

import semantics.domains._
import syntax.ast.Statement._
import syntax.ast._

/**
  * Created by asal on 15/01/2016.
  */
object IdIterExample extends Example {
  override val classDefs: Set[ClassDefinition] = Shared.stdClassDefs ++ Set(
    new ClassDefinition("IntSet", Map("data" -> (Class("Int"), Many)), Map())
  )

  override val pres: Set[SMem] = {
    val stack = Map("X" -> SetSymbol(-1))
    Set(
      SMem(stack, stack,
        SHeap.initial(Map(SetSymbol(-1) -> SSymbolDesc(Class("IntSet"), Opt, SUnowned)), Map(), Map(), Map(), Set()))
    )
  }

  override val prog: Statement = stmtSeq(
     assignVar("Y", SetLit(Seq()))
   , `for`("x", MSet(SetVar("X")), stmtSeq(
        assignVar("Y", Union(SetLit(Seq(Var("x"))), SetVar("Y")))
    ))
  )
}
