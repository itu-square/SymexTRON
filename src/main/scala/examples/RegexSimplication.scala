package examples

import semantics.domains.{SSymbolDesc, SHeap, SStack, SMem}
import syntax.ast.Statement._
import syntax.ast._


// Perhaps include a chapter about copying transformations for final OOPSLA submission
/**
  * Created by asal on 03/05/2016.
  */
trait RegexSimplication extends Example {
  override val classDefs =
    Shared.stdClassDefs ++
    Set (
      ClassDefinition("Regex", Map(), Map()),
      ClassDefinition("RegexRef", Map("value" -> (Class("Regex"), Single)), Map()),
      ClassDefinition("Char", Map(), Map(), superclass = Some(Class("Regex"))),
      ClassDefinition("CharA", Map(), Map(), superclass = Some(Class("Char"))),
      ClassDefinition("CharB", Map(), Map(), superclass = Some(Class("Char"))),
      ClassDefinition("CharC", Map(), Map(), superclass = Some(Class("Char"))),
      ClassDefinition("Epsilon", Map(), Map(), superclass = Some(Class("Regex"))),
      ClassDefinition("Alt", Map("left" -> (Class("RegexRef"), Single),
        "right" -> (Class("RegexRef"), Single)), Map(), superclass = Some(Class("Regex"))),
      ClassDefinition("Seq", Map("left" -> (Class("RegexRef"), Single),
        "right" -> (Class("RegexRef"), Single)), Map(), superclass = Some(Class("Regex"))),
      ClassDefinition("Star", Map("inner" -> (Class("RegexRef"), Single)), Map(), superclass = Some(Class("Regex")))
    )
  override val pres: Set[SMem] = Set(
    SMem(SStack.initial(Map("regex" -> SetSymbol(-1))),
      SHeap.initial(Map(SetSymbol(-1) -> SSymbolDesc(Class("RegexRef"), Single)),Map(),Map(), Map(), Set()))
  )
}

object RegexAltSimplification extends RegexSimplication {
  override val excludedBranches = Set(BranchPoint(0,0), BranchPoint(3,2))

  override val prog: Statement = {
    `for`("r_ref", MatchStar(Var("regex"), Class("RegexRef")), stmtSeq(
      loadField("r", Var("r_ref"), "value"),
      `for`("alt", Match(Var("r"), Class("Alt")), stmtSeq(
        loadField("alt_r", Var("alt"), "right"),
        loadField("alt_l", Var("alt"), "left"),
        `if`(Eq(Var("alt_r"), Var("alt_l")), stmtSeq(
          assignField(Var("r_ref"), "value", Var("alt_r"))
        ), stmtSeq())
      ))
    ))
  }
}

object RegexEpsSeqSimplification extends RegexSimplication {
  override val excludedBranches = Set(BranchPoint(0,0), BranchPoint(3,2), BranchPoint(7,2))

  override val prog: Statement = {
    `for`("r_ref", MatchStar(Var("regex"), Class("RegexRef")), stmtSeq(
      loadField("r", Var("r_ref"), "value"),
      `for`("seq", Match(Var("r"), Class("Seq")), stmtSeq(
        loadField("seq_r", Var("seq"), "right"),
        loadField("seq_l", Var("seq"), "left"),
        `for`("_", Match(Var("seq_r"), Class("Epsilon")), stmtSeq(
          assignField(Var("r_ref"), "value", Var("seq_l"))
        ))
      ))
    ))
  }
}

object RegexStarSimplification extends RegexSimplication {
  override val excludedBranches = Set(BranchPoint(0,0), BranchPoint(3,2), BranchPoint(7,2), BranchPoint(8,2))

  override val prog: Statement = {
    `for`("r_ref", MatchStar(Var("regex"), Class("RegexRef")), stmtSeq(
      loadField("r", Var("r_ref"), "value"),
      `for`("seq", Match(Var("r"), Class("Seq")), stmtSeq(
        loadField("seq_r", Var("seq"), "right"),
        loadField("seq_l", Var("seq"), "left"),
        `for`("star", Match(Var("seq_l"), Class("Star")),
          `for`("alt", Match(Var("seq_r"), Class("Alt")), stmtSeq(
            loadField("alt_r", Var("alt"), "right"),
            loadField("alt_l", Var("alt"), "left"),
            loadField("star_i", Var("star"), "inner"),
            `if`(Eq(Var("star_i"), Var("alt_l")),
              assignField(Var("r_ref"), "value", Var("star_i")),
              stmtSeq()
          ))
        )
      ))
    )))
  }
}