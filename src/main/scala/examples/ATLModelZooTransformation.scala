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
            `new`("fullName", Class("Concat")),
            assignField(Var("fullName"), "s1", Var("member_firstName")),
            assignField(Var("fullName"), "s2", Var("familyName")),
            assignField(Var("female"), "fullName", Var("fullName")),
            assignVar("persons", Union(Var("persons"), Var("female")))
          ),
          stmtSeq(
            `new`("male", Class("Male")),
            familyNameHelper(Var("member"), "familyName"),
            loadField("member_firstName", Var("member"), "firstName"),
            `new`("fullName", Class("Concat")),
            assignField(Var("fullName"), "s1", Var("member_firstName")),
            assignField(Var("fullName"), "s2", Var("familyName")),
            assignField(Var("male"), "fullName", Var("fullName")),
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
      ClassDefinition("Class", Map("isAbstract" -> FieldDefinition(Class("Any"), Opt, Ordinary), "attributes" -> FieldDefinition(Class("Attribute"), Many, Bidirectional(oppositeOf = "owner"))),
        Map("super" -> FieldDefinition(Class("Class"), Opt, Ordinary), "_Table" -> FieldDefinition(Class("Table"), Opt, Tracking)), superclass = Some(Class("Classifier"))),
      ClassDefinition("Attribute", Map(),
        Map("isMultivalued" -> FieldDefinition(Class("Any"), Opt, Ordinary), "type" -> FieldDefinition(Class("Class"), Single, Ordinary),
          "owner" -> FieldDefinition(Class("Class"), Single, Bidirectional(oppositeOf = "attributes")),
          "_Column" -> FieldDefinition(Class("Column"), Opt, Tracking)), superclass = Some(Class("NamedElt"))),
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
        `new`("idString", Class("String")),
        `new`("objectIdString", Class("String")),
        `for`("at", MatchStar(Var("package"), Class("Attribute")), stmtSeq(
          loadField("at_type", Var("at"), "type"),
          loadField("at_isMultivalued", Var("at"), "isMultivalued"),
          `for`("_", Match(Var("at_type"), Class("DataType")),
            `if`(Eq(Var("at_isMultivalued"), SetLit(Seq())),
              // rule SingleValuedDataTypeAttribute2Column
              stmtSeq(
                loadField("at_name", Var("at"), "name"),
                loadField("at_type_Type", Var("at_type"), "_Type"),
                `new`("column", Class("Column")),
                assignField(Var("column"), "name", Var("at_name")),
                assignField(Var("column"), "type", Var("at_type_Type")),
                assignField(Var("at"), "_Column", Var("column"))
              ),
              // rule MultiValuedDataTypeAttribute2Column
              stmtSeq(
                loadField("at_owner", Var("at"), "owner"),
                loadField("at_owner_name", Var("at_owner"), "name"),
                loadField("at_name", Var("at"), "name"),
                loadField("at_type_Type", Var("at_type"), "_Type"),
                `new`("tableName", Class("Concat")),
                assignField(Var("tableName"), "s1", Var("at_owner_name")),
                assignField(Var("tableName"), "s2", Var("at_name")),
                `new`("idName", Class("Concat")),
                assignField(Var("idName"), "s1", Var("at_owner_name")),
                assignField(Var("idName"), "s2", Var("idString")),
                `new`("id", Class("Column")),
                assignField(Var("id"), "name", Var("idName")),
                assignField(Var("id"), "type", Var("objectIdType")),
                `new`("value", Class("Column")),
                assignField(Var("value"), "name", Var("at_name")),
                assignField(Var("value"), "type", Var("at_type_Type")),
                `new`("table", Class("Table")),
                assignField(Var("table"), "name", Var("tableName")),
                assignField(Var("table"), "key", Var("id")), // !!! Actually missing in example ATL transformation
                assignField(Var("table"), "columns", Union(Var("id"), Var("value"))),
                loadField("schema_tables", Var("schema"), "tables"),
                assignField(Var("schema"), "tables", Union(Var("schema_tables"), Var("table")))
              )
            )),
          `for`("_", Match(Var("at_type"), Class("Class")),
            `if`(Eq(Var("at_isMultivalued"), SetLit(Seq())),
              // rule ClassAttribute2Column
              stmtSeq(
                loadField("at_name", Var("at"), "name"),
                `new`("column_name", Class("Concat")),
                assignField(Var("column_name"), "s1", Var("at_name")),
                assignField(Var("column_name"), "s2", Var("idString")),
                `new`("column", Class("Column")),
                assignField(Var("column"), "name", Var("column_name")),
                assignField(Var("column"), "type", Var("objectIdType")),
                assignField(Var("at"), "_Column", Var("column"))
              ),
              // rule MultiValuedClassAttribute2Column
              stmtSeq(
                loadField("at_owner", Var("at"), "owner"),
                loadField("at_owner_name", Var("at_owner"), "name"),
                loadField("at_name", Var("at"), "name"),
                `new`("tableName", Class("Concat")),
                assignField(Var("tableName"), "s1", Var("at_owner_name")),
                assignField(Var("tableName"), "s2", Var("at_name")),
                `new`("idName", Class("Concat")),
                assignField(Var("idName"), "s1", Var("at_owner_name")),
                assignField(Var("idName"), "s2", Var("idString")),
                `new`("id", Class("Column")),
                assignField(Var("id"), "name", Var("idName")),
                assignField(Var("id"), "type", Var("objectIdType")),
                `new`("foreignKey", Class("Column")),
                assignField(Var("foreignKey"), "name", Var("at_name")),
                assignField(Var("foreignKey"), "type", Var("objectIdType")),
                `new`("table", Class("Table")),
                assignField(Var("table"), "name", Var("tableName")),
                assignField(Var("table"), "key", Var("id")), // !!! Actually missing in example ATL transformation
                assignField(Var("table"), "columns", Union(Var("id"), Var("foreignKey"))),
                loadField("schema_tables", Var("schema"), "tables"),
                assignField(Var("schema"), "tables", Union(Var("schema_tables"), Var("table")))
              )))
        )),
        // rule Class2Table
        `for`("class", MatchStar(Var("package"), Class("Class")), stmtSeq(
          loadField("class_name", Var("class"), "name"),
          loadField("class_attributes", Var("class"), "attributes"),
          `new`("key", Class("Column")),
          assignField(Var("key"), "name", Var("objectIdString")),
          assignField(Var("key"), "type", Var("objectIdType")),
          assignVar("cols", Var("key")),
          `for`("at", MSet(Var("class_attributes")), stmtSeq(
            loadField("at_isMultivalued", Var("at"), "isMultivalued"),
            `if`(Eq(Var("at_isMultivalued"), SetLit(Seq())),
              stmtSeq(
                loadField("at_Column", Var("at"), "_Column"),
                assignVar("cols", Union(Var("cols"), Var("at_Column")))
              ),
              stmtSeq()
          ))),
          `new`("table", Class("Table")),
          assignField(Var("table"), "name", Var("class_name")),
          assignField(Var("table"), "key", Var("key")),
          assignField(Var("table"), "columns", Var("cols")), // TODO Handle bidirectional assignment in executors
          loadField("schema_tables", Var("schema"), "tables"),
          assignField(Var("schema"), "tables", Union(Var("schema_tables"), Var("table")))
        ))
      )
    }
  }
}
