package examples

import syntax.ast.Statement._
import syntax.ast._

/**
  * Created by asal on 15/01/2016.
  */
object ContactBookExample extends Example {
  override val classDefs: Set[ClassDefinition] = Shared.stdClassDefs ++ Set(
    new ClassDefinition("ContactBook", Map("persons" -> (Class("Person"), Opt)), Map())
  , new ClassDefinition("Person", Map("age" -> (Class("Age"), Single),
                                      "name" -> (Class("String"), Single)), Map())
  , new ClassDefinition("Age", Map(), Map())
  , new ClassDefinition("Adult", Map(), Map(), Some(Class("Age")))
  , new ClassDefinition("Child", Map(), Map(), Some(Class("Age")))
  , new ClassDefinition("Invited", Map("name" -> (Class("String"), Single)), Map())
  )
  override val pres: Set[SMem] = Set(SMem(Map("contactbook" -> SetLit(Symbol(-1))),
                                     SHeap(Map(-1 -> SpatialDesc(Class("ContactBook"), AbstractDesc, Map(), Map())), Set(), Set())))
  override val prog: Statement = stmtSeq(
     assignVar("invitationlist", SetLit())
   , `for`("person'", MatchStar(SetLit(Var("contactbook")), Class("Person")), stmtSeq(
      assignVar("isadult", SetLit())
    , loadField("person_age", SetLit(Var("person")), "age")
    , loadField("person_name", SetLit(Var("person")), "name")
    , `for`("age", Match(SetLit(Var("person_age")), Class("Adult")), stmtSeq(
        `new`("isadult", Class("Any"))
      ))
    , `if`(stmtSeq(), Not(Eq(SetVar("isadult"), SetLit())) -> stmtSeq(
        `new`("invited", Class("Invited"))
      , assignField(SetLit(Var("invited")), "name", SetLit(Var("person_name")))
      , assignVar("invitationlist", Union(SetVar("invitationlist"), SetLit(Var("invited"))))
      ))
    ))
  )
}
