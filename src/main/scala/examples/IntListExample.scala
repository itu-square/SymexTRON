package examples

import semantics.domains._
import syntax.ast._
import syntax.ast.Statement._

/**
  * Created by asal on 15/01/2016.
  */
object IntListExample extends Example {
  override val classDefs: Set[ClassDefinition] = Shared.stdClassDefs ++ Set(
    new ClassDefinition("IntList", Map("next" -> (Class("IntList"), Opt)),
                                   Map("data" -> (Class("Int"), Single)))
  )
  override val pres: Set[SMem] = Set(
    SMem(Map("list" -> SetSymbol(-1), "elem" -> SetLit(Symbol(-2))),
             SHeap.initial(Map(SetSymbol(-1) -> SSymbolDesc(Class("IntList"), Opt, SUnowned)), Map(Symbol(-2) -> UnknownLoc(Class("Int"), SUnowned)), Map(), Map(), Set()))
  )

  override val prog: Statement = stmtSeq(
     assignVar("containselem", SetLit())
   , `for`("sublist", MatchStar(SetVar("list"), Class("IntList")), stmtSeq(
        loadField("sublist_data", SetLit(Var("sublist")), "data")
        ,`if`(Eq(SetLit(Var("elem")), SetLit(Var("sublist_data")))
             , `new`("containselem", Class("Any"))
             , stmtSeq())
    ))
  )
}
