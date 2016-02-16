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
    SMem(Map("list" -> SetSymbol(-1), "elem" -> SetLit(Seq(Symbol(-2)))),
             SHeap.initial(Map(SetSymbol(-1) -> SSymbolDesc(Class("IntList"), Opt, SUnowned, Map())), Map(Symbol(-2) -> UnknownLoc(Class("Int"), SUnowned, Map())), Map(), Map(), Set()))
  )

  override val prog: Statement = stmtSeq(
     assignVar("containselem", SetLit(Seq()))
   , `for`("sublist", MatchStar(SetVar("list"), Class("IntList")), stmtSeq(
        loadField("sublist_data", SetLit(Seq(Var("sublist"))), "data")
        ,`if`(Eq(SetLit(Seq(Var("elem"))), SetLit(Seq(Var("sublist_data"))))
             , `new`("containselem", Class("Any"))
             , stmtSeq())
    ))
  )
}
