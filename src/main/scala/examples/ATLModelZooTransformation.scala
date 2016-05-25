package examples

import semantics.domains.{SSymbolDesc, SStack, SHeap, SMem}
import syntax.ast
import syntax.ast._
import syntax.ast.Statement._

/**
  * Created by asal on 25/05/2016.
  */
trait ATLModelZooTransformation extends Example { }

object FamiliesToPersonsTransformation extends ATLModelZooTransformation {
  override val classDefs = Shared.stdClassDefs ++ Set (
    ClassDefinition("Family", Map("father" -> (Class("Member"), Single),
                                  "mother" -> (Class("Member"), Single),
                                  "sons" -> (Class("Member"), Many),
                                  "daughters" -> (Class("Member"), Many)),
                              Map("lastName" -> (Class("String"), Single)), superclass = Some(Class("Any"))),
    ClassDefinition("Member", Map(), Map("firstName" -> (Class("String"), Single),
                                         "familyFather" -> (Class("Family"), Opt),
                                         "familyMother" -> (Class("Family"), Opt),
                                         "familySon" -> (Class("Family"), Opt),
                                         "familyDaughter" -> (Class("Family"), Opt)), superclass = Some(Class("Any"))),
    ClassDefinition("Person", Map(), Map("fullName" -> (Class("String"), Single)), superclass = Some(Class("Any"))),
    ClassDefinition("Male", Map(), Map(), superclass = Some(Class("Person"))),
    ClassDefinition("Female", Map(), Map(), superclass = Some(Class("Person")))
  )
  override val pres: Set[SMem] = Set(SMem(SStack.initial(Map("families" -> SetSymbol(-1))),
    SHeap.initial(Map(SetSymbol(-1) -> SSymbolDesc(Class("Family"), Many)), Map(), Map(), Map(), Set())))
  override val prog: Statement = {
    def isFemaleHelper(self: SetExpr[IsProgram.type], outVar: Vars): Statement = stmtSeq(
      loadField("self_familyMother", self, "familyMother"),
      loadField("self_familyDaughter", self, "familyDaughter"),
      `if`(Not(Eq(Var("self_familyMother"), SetLit(Seq()))),
        `new`(outVar, Class("Any")),
        `if`(Not(Eq(Var("self_familyDaughter"), SetLit(Seq()))),
          `new`(outVar, Class("Any")),
          assignVar(outVar, SetLit(Seq()))
        )
      )
    )
    def familyNameHelper(self: SetExpr[IsProgram.type], outVar: Vars): Statement = stmtSeq(
      loadField("self_familyFather", self, "familyFather"),
      loadField("self_familyMother", self, "familyMother"),
      loadField("self_familySon", self, "familySon"),
      loadField("self_familyDaughter", self, "familyDaughter"),
      `if`(Not(Eq(Var("self_familyFather"), SetLit(Seq()))),
        loadField(outVar, Var("self_familyFather"), "lastName"),
        `if`(Not(Eq(Var("self_familyMother"), SetLit(Seq()))),
          loadField(outVar, Var("self_familyMother"), "lastName"),
          `if`(Not(Eq(Var("self_familySon"), SetLit(Seq()))),
            loadField(outVar, Var("self_familySon"), "lastName"),
            loadField(outVar, Var("self_familyDaughter"), "lastName")
        )
      ))
    )
    stmtSeq(
      assignVar("persons", SetLit(Seq())),
      `for`("member", MatchStar(Var("families"), Class("Member")), stmtSeq(
        isFemaleHelper(Var("member"), "isFemale"),
        `if`(Eq(Var("isFemale"), SetLit(Seq())),
          stmtSeq(
            `new`("female", Class("Female")),
            familyNameHelper(Var("member"), "familyName"),
            loadField("member_firstName", Var("member"), "firstName"),
            `new`("concat", Class("Concat")),
            assignField(Var("concat"), "left", Var("member_firstName")),
            assignField(Var("concat"), "right", Var("familyName")),
            assignField(Var("female"), "fullName", Var("concat")),
            assignVar("persons", Union(Var("persons"), Var("female")))
          ),
          stmtSeq(
            `new`("male", Class("Male")),
            familyNameHelper(Var("member"), "familyName"),
            loadField("member_firstName", Var("member"), "firstName"),
            `new`("concat", Class("Concat")),
            assignField(Var("concat"), "left", Var("member_firstName")),
            assignField(Var("concat"), "right", Var("familyName")),
            assignField(Var("male"), "fullName", Var("concat")),
            assignVar("persons", Union(Var("persons"), Var("male")))
          )
        )
      ))
    )
  }

  object ClassToRelationalTransformation extends ATLModelZooTransformation {
    override val classDefs: Set[ClassDefinition] = Shared.stdClassDefs ++ Set(
      // Class
      ClassDefinition("NamedElt", Map(), Map("name" -> (Class("String"), Single))),
      ClassDefinition("Classifier", Map(), Map(), superclass = Some(Class("NamedElt"))),
      ClassDefinition("DataType", Map(), Map(), superclass = Some(Class("Classifier"))),
      ClassDefinition("Class", Map("isAbstract" -> (Class("Any"), Opt), "attributes" -> (Class("Attribute"), Many)), Map("super" -> (Class("Class"), Opt)), superclass = Some(Class("Classifier"))),
      ClassDefinition("Attribute", Map("multivalued" -> (Class("Any"), Opt)), Map("type" -> (Class("Class"), Single)), superclass = Some(Class("NamedElt"))),
      ClassDefinition("Package", Map("classes" -> (Class("Class"), Many)), Map()),
      // Relational
      ClassDefinition("Named", Map(), Map("name" -> (Class("String"), Single))),
      ClassDefinition("Table", Map("columns" -> (Class("Column"), Many)), Map("key" -> (Class("Column"), Single)), superclass = Some(Class("Named"))),
      ClassDefinition("Column", Map(), Map("type" -> (Class("Type"), Single)), superclass = Some(Class("Named"))),
      ClassDefinition("Type", Map(), Map(), superclass = Some(Class("Type"))),
      ClassDefinition("Schema", Map("tables" -> (Class("Table"), Many)), Map())
    )
    override val pres: Set[SMem] = ???
    override val prog: Statement = ???
  }
}
