package examples

import semantics.domains._
import syntax.ast._
import syntax.ast.Statement._

/**
  * Created by asal on 15/01/2016.
  */
trait BlogPostFeedExample extends Example {
  override val pres: Set[SMem] = {
    val stack = Map("post" -> SetLit(Seq(Symbol(-1))))
    Set(
      SMem(stack, stack, SHeap.initial(Map(), Map(Symbol(-1) -> UnknownLoc(Class("Post"), SUnowned, Set())), Map(), Map(), Set()))
    )
  }

  override val classDefs: Set[ClassDefinition] = Shared.stdClassDefs ++ Set(
      new ClassDefinition("Title", Map(), Map("value" -> (Class("String"), Single)))
    , new ClassDefinition("CapitalisedTitle", Map(), Map(), Some(Class("Title")))
    , new ClassDefinition("Timestamp", Map(), Map("value" -> (Class("Int"), Single)))
    , new ClassDefinition("Post", Map(), Map())
    , new ClassDefinition("SinglePost", Map("title" -> (Class("Title"), Single),
                                            "timestamp" -> (Class("Timestamp"), Single)), Map(), Some(Class("Post")))
    , new ClassDefinition("AggregatePost", Map("content" -> (Class("Post"), Many)), Map(), Some(Class("Post")))
  )
}

object BlogPostFeedTimestampsExample extends BlogPostFeedExample {
  override val prog: Statement = stmtSeq(
     assignVar("timestamps", SetLit(Seq()))
   , `for`("ts", MatchStar(SetLit(Seq(Var("post"))), Class("Timestamp")), stmtSeq(
        assignVar("timestamps", Union(SetVar("timestamps"), SetLit(Seq(Var("ts")))))
    ))
  )
}

object BlogPostFeedCapitaliseTitlesExample extends BlogPostFeedExample {
  override val prog: Statement = `for`("sp", MatchStar(SetLit(Seq(Var("post"))), Class("SinglePost")), stmtSeq(
      loadField("sp_title", SetVar("sp"), "title")
    , loadField("sp_title_value", SetVar("sp_title"), "value")
    , `new`("new_sp_title", Class("CapitalisedTitle"))
    , assignField(SetVar("new_sp_title"), "value", SetVar("sp_title_value"))
    , assignField(SetVar("sp"), "title", SetVar("new_sp_title"))
  ))
}