package examples

import semantics.domains._
import syntax.ast
import syntax.ast._
import syntax.ast.Statement._

/**
  * Created by asal on 25/05/2016.
  */
trait ATLModelZooTransformation extends Example { }

object FamiliesToPersonsTransformation extends ATLModelZooTransformation {
  override val classDefs = Shared.stdClassDefs ++ Set (
    ClassDefinition("Family", Map("father" -> FieldDefinition(Class("Member"), Single, Bidirectional(oppositeOf = "familyFather")),
                                  "mother" -> FieldDefinition(Class("Member"), Single, Bidirectional(oppositeOf = "familyMother")),
                                  "sons" -> FieldDefinition(Class("Member"), Many, Bidirectional(oppositeOf = "familySon")),
                                  "daughters" -> FieldDefinition(Class("Member"), Many, Bidirectional(oppositeOf = "familyDaughter"))),
                              Map("lastName" -> FieldDefinition(Class("String"), Single, Ordinary)), superclass = Some(Class("Any"))),
    ClassDefinition("Member", Map(), Map("firstName" -> FieldDefinition(Class("String"), Single, Ordinary),
                                         "familyFather" -> FieldDefinition(Class("Family"), Opt, Bidirectional(oppositeOf = "father")),
                                         "familyMother" -> FieldDefinition(Class("Family"), Opt, Bidirectional(oppositeOf = "mother")),
                                         "familySon" -> FieldDefinition(Class("Family"), Opt, Bidirectional(oppositeOf = "sons")),
                                         "familyDaughter" -> FieldDefinition(Class("Family"), Opt, Bidirectional(oppositeOf = "daughters"))), superclass = Some(Class("Any"))),
    ClassDefinition("Person", Map(), Map("fullName" -> FieldDefinition(Class("String"), Single, Ordinary)), superclass = Some(Class("Any"))),
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
            assignField(Var("concat"), "s1", Var("member_firstName")),
            assignField(Var("concat"), "s2", Var("familyName")),
            assignField(Var("female"), "fullName", Var("concat")),
            assignVar("persons", Union(Var("persons"), Var("female")))
          ),
          stmtSeq(
            `new`("male", Class("Male")),
            familyNameHelper(Var("member"), "familyName"),
            loadField("member_firstName", Var("member"), "firstName"),
            `new`("concat", Class("Concat")),
            assignField(Var("concat"), "s1", Var("member_firstName")),
            assignField(Var("concat"), "s2", Var("familyName")),
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
      ClassDefinition("NamedElt", Map(), Map("name" -> FieldDefinition(Class("String"), Single, Ordinary))),
      ClassDefinition("Classifier", Map(), Map(), superclass = Some(Class("NamedElt"))),
      ClassDefinition("DataType", Map(), Map("_Type" -> FieldDefinition(Class("Type"), Opt, Tracking)), superclass = Some(Class("Classifier"))),
      ClassDefinition("Class", Map("isAbstract" -> FieldDefinition(Class("Any"), Opt, Ordinary), "attributes" -> FieldDefinition(Class("Attribute"), Many, Ordinary)),
        Map("super" -> FieldDefinition(Class("Class"), Opt, Ordinary), "_Table" -> FieldDefinition(Class("Table"), Opt, Tracking)), superclass = Some(Class("Classifier"))),
      ClassDefinition("Attribute", Map("multivalued" -> FieldDefinition(Class("Any"), Opt, Ordinary)),
        Map("type" -> FieldDefinition(Class("Class"), Single, Ordinary), "_Column" -> FieldDefinition(Class("Column"), Opt, Tracking)), superclass = Some(Class("NamedElt"))),
      ClassDefinition("Package", Map("classifiers" -> FieldDefinition(Class("Classifier"), Many, Ordinary)), Map()),
      // Relational
      ClassDefinition("Named", Map(), Map("name" -> FieldDefinition(Class("String"), Single, Ordinary))),
      ClassDefinition("Table", Map("columns" -> FieldDefinition(Class("Column"), Many, Ordinary)),
        Map("key" -> FieldDefinition(Class("Column"), Single, Ordinary)), superclass = Some(Class("Named"))),
      ClassDefinition("Column", Map(), Map("type" -> FieldDefinition(Class("Type"), Single, Ordinary)), superclass = Some(Class("Named"))),
      ClassDefinition("Type", Map(), Map(), superclass = Some(Class("Type"))),
      ClassDefinition("Schema", Map("tables" -> FieldDefinition(Class("Table"), Many, Ordinary), "types" -> FieldDefinition(Class("Type"), Many, Ordinary)), Map())
    )
    override val pres: Set[SMem] = Set(SMem(SStack.initial(Map("package" -> SetLit(Seq(Symbol(-1))))),
      SHeap.initial(Map(), Map(Symbol(-1) -> UnknownLoc(Class("Package"), Set())), Map(), Map(), Set())))
    override val prog: Statement = {
      def objectIdTypeHelper(outVar: Vars) = stmtSeq(
        assignVar(outVar, SetLit(Seq())),
        `for`("dt", MatchStar(Var("package"), Class("DataType")),
          stmtSeq(
            loadField("dt_name", Var("dt"), "name"),
            `if`(And(Not(Eq(Var(outVar), SetLit(Seq()))), Eq(Var("dt_name"), Var("integer_name"))),
              loadField(outVar, Var("dt"), "_Type"),
              stmtSeq()
            )
          )
        ))
      stmtSeq(
        // Create new Schema to hold things
        `new`("schema", Class("Schema")),
        // rule DataType2Type
        `for`("dt", MatchStar(Var("package"), Class("DataType")), stmtSeq(
            `new`("type", Class("Type")),
            loadField("dt_name", Var("dt"), "name"),
            assignField(Var("type"), "name", Var("dt_name")),
            assignField(Var("dt"), "_Type", Var("type")),
            loadField("schema_types", Var("schema"), "types"),
            assignField(Var("schema"), "types", Union(Var("schema_types"), Var("type")))
          )
        ),
        objectIdTypeHelper("objectIdType"),
        // rule SingleValuedDataTypeAttribute2Column
        stmtSeq(),
        // rule MultiValuedDataTypeAttribute2Column
        stmtSeq(),
        // rule ClassAttribute2Column
        stmtSeq(),
        // rule MultiValuedClassAttribute2Column
        stmtSeq(),
        // rule Class2Table
        stmtSeq()
      )
    }
  }
}
