package examples
package evaluation

import semantics.domains._
import syntax.ast._
import Statement._

object Refactoring {


  val renameFieldInput: SMem = {
        val packageId        = -1
        val classId          = -2
        val oldFieldId       = -3
        val newFieldId       = -4
        val packageClassesId = -5
        val classFieldsId    = -6
        val classMethodsId   = -7
        val classNameId      = -8
        val classSuperId     = -9

        val inputStack = Map("package" -> SetLit(Seq(Symbol(packageId))), "class" -> SetLit(Seq(Symbol(classId))),
                             "old_field" -> SetLit(Seq(Symbol(oldFieldId))), "new_field" -> SetLit(Seq(Symbol(newFieldId))))
        val inputHeap = SHeap.initial(
          Map(   SetSymbol(packageClassesId) -> SSymbolDesc(Class("Class"), Many, SOwned(Loc(packageId), "classes"))
               , SetSymbol(classFieldsId) -> SSymbolDesc(Class("Field"), Many, SOwned(Loc(classId), "fields"))
               , SetSymbol(classSuperId) -> SSymbolDesc(Class("Class"), Opt, SOwned(Loc(packageId), "classes"))
               )
          , Map(Symbol(packageId)  -> Loced(Loc(packageId)),
              Symbol(classId)    -> Loced(Loc(classId)),
              Symbol(oldFieldId) -> UnknownLoc(Class("Field"), SOwned(Loc(classId), "fields")),
              Symbol(newFieldId) -> UnknownLoc(Class("Field"), SUnowned),
              Symbol(classNameId) -> UnknownLoc(Class("String"), SUnowned))
          , Map(Loc(packageId) -> Unowned, Loc(classId) -> Owned(Loc(packageId), "classes"))
          , Map(Loc(packageId) -> SpatialDesc(Class("Package"), ExactDesc, Map("classes" -> Union(SetSymbol(packageClassesId), SetLit(Seq(Symbol(classId))))), Map(), Map()),
                Loc(classId) -> SpatialDesc(Class("Class"), ExactDesc, Map("fields" -> Union(SetSymbol(classFieldsId), SetLit(Seq(Symbol(oldFieldId)))),
                                                                                "methods" -> SetSymbol(classMethodsId))
                                                                          , Map("name" -> SetSymbol(classNameId),
                                                                                "super" -> SetSymbol(classSuperId)), Map()))
             , Set(
                   Eq(SetLit(Seq()), ISect(SetSymbol(packageClassesId), SetLit(Seq(Symbol(classId))))),
                   Eq(SetLit(Seq()), ISect(SetSymbol(classFieldsId), SetLit(Seq(Symbol(oldFieldId)))))
                 )
        )
        SMem(inputStack, inputStack, inputHeap)
  }

  // Input:: package: Package, class: Class, old_field : Field, new_field : Field
  val renameFieldAst: Statement = stmtSeq(
    loadField("class_fields", SetLit(Seq(Var("class"))), "fields")
  , assignField(SetLit(Seq(Var("class"))), "fields", Union(Diff(SetVar("class_fields"), SetLit(Seq(Var("old_field")))), SetLit(Seq(Var("new_field")))))
  , `for`("faexpr", MatchStar(SetLit(Seq(Var("package"))), Class("FieldAccessExpr")), stmtSeq(
            loadField("faexpr_field_name", SetLit(Seq(Var("faexpr"))), "field_name")
          , loadField("old_field_name", SetLit(Seq(Var("old_field"))), "name")
          , loadField("faexpr_target", SetLit(Seq(Var("faexpr"))), "target")
          , loadField("faexpr_target_type", SetLit(Seq(Var("faexpr_target"))), "type")
          , `if`(And(Eq(SetLit(Seq(Var("faexpr_field_name"))), SetLit(Seq(Var("old_field_name")))),
                   Eq(SetVar("class"), SetVar("faexpr_target_type")))
                 , stmtSeq(
                       loadField("new_field_name", SetLit(Seq(Var("new_field"))), "name")
                     , assignField(SetLit(Seq(Var("faexpr"))), "name", SetLit(Seq(Var("new_field_name")))))
                 , stmtSeq()
               )
      ))
  )

  val renameMethodInput: SMem = {
        val packageId        = -1
        val classId          = -2
        val oldMethodId      = -3
        val newMethodId      = -4
        val packageClassesId = -5
        val classFieldsId    = -6
        val classMethodsId   = -7
        val classNameId      = -8
        val classSuperId     = -9

        val inputStack = Map("package" -> SetLit(Seq(Symbol(packageId))), "class" -> SetLit(Seq(Symbol(classId))),
                             "old_method" -> SetLit(Seq(Symbol(oldMethodId))), "new_method" -> SetLit(Seq(Symbol(newMethodId))))
        val inputHeap = SHeap.initial(
          Map(   SetSymbol(packageClassesId) -> SSymbolDesc(Class("Class"), Many, SOwned(Loc(packageId), "classes"))
            , SetSymbol(classFieldsId) -> SSymbolDesc(Class("Field"), Many, SOwned(Loc(classId), "fields"))
            , SetSymbol(classSuperId) -> SSymbolDesc(Class("Class"), Opt, SOwned(Loc(packageId), "classes"))
          ),
          Map(Symbol(packageId)  -> Loced(Loc(packageId)),
            Symbol(classId)    -> Loced(Loc(classId)),
            Symbol(oldMethodId) -> UnknownLoc(Class("Method"), SOwned(Loc(classId), "methods")),
            Symbol(newMethodId) -> UnknownLoc(Class("Method"), SUnowned),
            Symbol(classNameId) -> UnknownLoc(Class("String"), SUnowned)),
          Map(Loc(packageId) -> Unowned, Loc(classId) -> Owned(Loc(packageId), "classes")),
          Map(Loc(packageId) -> SpatialDesc(Class("Package"), ExactDesc, Map("classes" -> Union(SetSymbol(packageClassesId), SetLit(Seq(Symbol(classId))))), Map(), Map()),
            Loc(classId) -> SpatialDesc(Class("Class"), ExactDesc
              , Map("fields" -> SetSymbol(classFieldsId),
                    "methods" -> Union(SetSymbol(classMethodsId), SetLit(Seq(Symbol(oldMethodId)))))
              , Map("name" -> SetSymbol(classNameId),
                    "super" -> SetSymbol(classSuperId)), Map()))
          , Set(
            Eq(SetLit(Seq()), ISect(SetSymbol(packageClassesId), SetLit(Seq(Symbol(classId))))),
            Eq(SetLit(Seq()), ISect(SetSymbol(classMethodsId), SetLit(Seq(Symbol(oldMethodId)))))
          )
        )
        SMem(inputStack, inputStack, inputHeap)
  }

  // Input:: package: Package, class: Class, old_method : Method, new_method : Method
  //Assumes overloading is allowed (but arity must be different), things are semantically checked, and that the transformation is applicable
  val renameMethodAst: Statement  = stmtSeq(
     loadField("class_methods", SetLit(Seq(Var("class"))), "methods")
   , assignField(SetLit(Seq(Var("class"))), "methods", Union(Diff(SetVar("class_methods"), SetLit(Seq(Var("old_method")))), SetLit(Seq(Var("new_method")))))
   , `for`("mcexpr", MatchStar(SetLit(Seq(Var("package"))), Class("MethodCallExpr")), stmtSeq(
          loadField("mcexpr_method_name", SetLit(Seq(Var("mcexpr"))), "method_name")
        , loadField("old_method_name", SetLit(Seq(Var("old_method"))), "name")
        , loadField("old_method_params", SetLit(Seq(Var("old_method"))), "params")
        , loadField("mcexpr_target", SetLit(Seq(Var("mcexpr"))), "target")
        , loadField("mcexpr_target_type", SetLit(Seq(Var("mcexpr_target"))), "type")
        , loadField("mcexpr_args", SetLit(Seq(Var("mcexpr"))), "args")
        , `new`("paramsmatched", Class("Any"))
        , `for`("omp", MSet(SetVar("old_method_params")), stmtSeq(
              assignVar("parammatched", SetLit(Seq()))
            , loadField("omp_name", SetLit(Seq(Var("omp"))), "name")
            , `for`("mcea", MSet(SetVar("mcexpr_args")), stmtSeq(
                 loadField("mcea_name", SetLit(Seq(Var("mcea"))), "name"),
                 `if`(Eq(SetLit(Seq(Var("omp_name"))), SetLit(Seq(Var("mcea_name")))),
                      assignVar("parammatched", SetVar("paramsmatched"))
                    , stmtSeq())
               ))
            , `if`(Eq(SetVar("parammatched"), SetLit(Seq()))
                  , assignVar("paramsmatched", SetLit(Seq()))
                  , stmtSeq())
          ))
        , `if`(And(And(Eq(SetLit(Seq(Var("mcexpr_method_name"))), SetLit(Seq(Var("old_method_name")))),
                Eq(SetVar("class"), SetVar("mcexpr_target_type"))),
                  or(And(Eq(SetVar("old_method_params"), SetLit(Seq())), Eq(SetVar("mcexpr_args"), SetLit(Seq()))),
                     Not(Eq(SetVar("paramsmatched"), SetLit(Seq())))))
              , stmtSeq(loadField("new_method_name", SetLit(Seq(Var("new_method"))), "name")
                       , assignField(SetLit(Seq(Var("mcexpr"))), "name", SetLit(Seq(Var("new_method_name")))))
              , stmtSeq()
              )
        ))
   )
   val extractSuperclassInput: SMem = {
         val packageId        = -1
         val class1Id         = -2
         val class2Id         = -3
         val scnameId         = -4
         val packageClassesId = -5

         val inputStack = Map("package" -> SetLit(Seq(Symbol(packageId))), "class1" -> SetLit(Seq(Symbol(class1Id))),
                              "class2" -> SetLit(Seq(Symbol(class2Id))), "sc_name" -> SetLit(Seq(Symbol(scnameId))))
         val inputHeap = SHeap.initial(
           Map(SetSymbol(packageClassesId) -> SSymbolDesc(Class("Class"), Many, SOwned(Loc(packageId), "classes"))),
           Map(
             Symbol(packageId) -> Loced(Loc(packageId)),
             Symbol(scnameId) -> UnknownLoc(Class("String"), SUnowned),
             Symbol(class1Id) -> UnknownLoc(Class("Class"), SOwned(Loc(packageId), "classes")),
             Symbol(class2Id) -> UnknownLoc(Class("Class"), SOwned(Loc(packageId), "classes"))  ),
           Map(Loc(packageId) -> Unowned),
           Map(Loc(packageId) -> SpatialDesc(Class("Package"), ExactDesc, Map("classes" -> Union(Union(SetSymbol(packageClassesId), SetLit(Seq(Symbol(class2Id)))), SetLit(Seq(Symbol(class2Id))))), Map(), Map())),
           Set()
         )
         SMem(inputStack, inputStack, inputHeap)
   }

  // Input:: class1 : Class, class2 : Class, sc_name : String
  val extractSuperclassAst: Statement = stmtSeq(
      `new`("sclass", Class("Class"))
    , loadField("package_classes", SetLit(Seq(Var("package"))), "classes")
    , assignField(SetLit(Seq(Var("package"))), "classes", Union(SetVar("package_classes"), SetLit(Seq(Var("sclass")))))
    , assignField(SetLit(Seq(Var("class1"))), "super", SetLit(Seq(Var("sclass"))))
    , assignField(SetLit(Seq(Var("class2"))), "super", SetLit(Seq(Var("sclass"))))
    , assignField(SetLit(Seq(Var("sclass"))), "name", SetLit(Seq(Var("sc_name"))))
    // Pull up relevant fields
    , assignVar("new_sclass_fields", SetLit(Seq()))
    , assignVar("rem_class1_fields", SetLit(Seq()))
    , assignVar("rem_class2_fields", SetLit(Seq()))
    , loadField("class1_fields", SetLit(Seq(Var("class1"))), "fields")
    , loadField("class2_fields", SetLit(Seq(Var("class2"))), "fields")
    , `for`("c1f", MSet(SetVar("class1_fields")), stmtSeq(
            `for`("c2f", MSet(SetVar("class2_fields")), stmtSeq(
                     loadField("c1f_name", SetLit(Seq(Var("c1f"))), "name")
                   , loadField("c2f_name", SetLit(Seq(Var("c2f"))), "name")
                   , loadField("c1f_type", SetLit(Seq(Var("c1f"))), "type")
                   , loadField("c2f_type", SetLit(Seq(Var("c2f"))), "type")
                   , `if`(And(Eq(SetLit(Seq(Var("c1f_name"))), SetLit(Seq(Var("c2f_name")))),
                             Eq(SetLit(Seq(Var("c2f_type"))), SetLit(Seq(Var("c2f_type")))))
                         , stmtSeq(
                            `new`("scf", Class("Field"))
                           , assignField(SetLit(Seq(Var("scf"))), "name", SetLit(Seq(Var("c1f_name"))))
                           , assignField(SetLit(Seq(Var("scf"))), "type", SetLit(Seq(Var("c1f_type"))))
                           , assignVar("new_sclass_fields", Union(SetVar("new_sclass_fields"), SetLit(Seq(Var("scf")))))
                           , assignVar("rem_class1_fields", Union(SetVar("rem_class1_fields"), SetLit(Seq(Var("c1f")))))
                           , assignVar("rem_class2_fields", Union(SetVar("rem_class2_fields"), SetLit(Seq(Var("c2f")))))
                          )
                         , stmtSeq())
                ))
         ))
   , assignField(SetLit(Seq(Var("class1"))), "fields", Diff(SetVar("class1_fields"), SetVar("rem_class1_fields")))
   , assignField(SetLit(Seq(Var("class2"))), "fields", Diff(SetVar("class2_fields"), SetVar("rem_class2_fields")))
   , assignField(SetLit(Seq(Var("sclass"))), "fields", SetVar("new_sclass_fields"))
  )

  val replaceDelegationWithInheritanceInput: SMem = {
        val classId          = -1
        val fieldId          = -2
        val classFieldsId    = -3
        val classMethodsId   = -4
        val classNameId      = -5
        val classSuperId     = -6

        val inputStack = Map("class" -> SetLit(Seq(Symbol(classId))),
                             "field" -> SetLit(Seq(Symbol(fieldId))))
        val inputHeap = SHeap.initial(
          Map(SetSymbol(classFieldsId) -> SSymbolDesc(Class("Field"), Many, SOwned(Loc(classId), "fields")),
              SetSymbol(classMethodsId) -> SSymbolDesc(Class("Method"), Many, SOwned(Loc(classId), "methods")),
              SetSymbol(classSuperId) -> SSymbolDesc(Class("String"), Opt, SUnowned)),
          Map(Symbol(classId) -> Loced(Loc(classId)),
              Symbol(fieldId) -> UnknownLoc(Class("Field"), SOwned(Loc(classId), "fields")),
              Symbol(classNameId) -> UnknownLoc(Class("String"), SUnowned)),
          Map(Loc(classId) -> Unowned),
          Map(Loc(classId) -> SpatialDesc(Class("Class"), ExactDesc
            , Map("fields" -> Union(SetSymbol(classFieldsId), SetLit(Seq(Symbol(fieldId))))
              ,   "methods" -> SetSymbol(classMethodsId)), Map("name" -> SetLit(Seq(Symbol(classNameId))), "super" -> SetSymbol(classSuperId)), Map())),
          Set(Eq(SetLit(Seq()), ISect(SetSymbol(classFieldsId), SetLit(Seq(Symbol(fieldId))))))
        )
        SMem(inputStack, inputStack, inputHeap)
  }

  // Assumes that methods that have the same name as the delegate are delegated methods and that field is private
  // class: Class, field : Field
  val replaceDelegationWithInheritanceAst : Statement = stmtSeq(
      loadField("class_fields", SetLit(Seq(Var("class"))), "fields")
    , loadField("field_type", SetLit(Seq(Var("field"))), "type")
    , assignField(SetLit(Seq(Var("class"))), "super", SetLit(Seq(Var("field_type"))))
    // Remove all delegated methods
    , loadField("field_type_methods", SetLit(Seq(Var("field_type"))), "methods")
    , loadField("class_methods", SetLit(Seq(Var("class"))), "methods")
    , assignVar("class_new_methods", SetLit(Seq()))
    , `for`("ftm", MSet(SetVar("field_type_methods")), stmtSeq(
        `for`("cm", MSet(SetVar("class_methods")), stmtSeq(
              loadField("ftm_name", SetLit(Seq(Var("ftm"))), "name")
            , loadField("cm_name", SetLit(Seq(Var("cm"))), "name")
            , `if`(Not(Eq(SetLit(Seq(Var("ftm_name"))), SetLit(Seq(Var("cm_name")))))
                  , assignVar("class_new_methods", Union(SetVar("class_new_methods"), SetLit(Seq(Var("cm")))))
                  , stmtSeq())
          ))
      ))
    , assignField(SetLit(Seq(Var("class"))), "methods", SetVar("class_new_methods"))
    // Replace other delegations with calls to the object itself
    , `for`("mcexpr", MatchStar(SetLit(Seq(Var("class"))), Class("MethodCallExpr")), stmtSeq(
          loadField("mcexpr_target", SetLit(Seq(Var("mcexpr"))), "target")
        , assignVar("MCEXPR_TARGET", SetLit(Seq()))
        , `for`("mcx", Match(SetLit(Seq(Var("mcexpr_target"))), Class("FieldAccessExpr")),
                  assignVar("MCEXPR_TARGET", SetLit(Seq(Var("mcx"))))
           )
        , `if`(not(Eq(SetVar("MCEXPR_TARGET"), SetLit(Seq())))
              , stmtSeq(
                  loadField("mcexpr_target_target", SetLit(Seq(Var("mcexpr_target"))), "target")
                , loadField("mcexpr_target_target_type", SetLit(Seq(Var("mcexpr_target_target"))), "type")
                , loadField("mcexpr_target_field_name", SetLit(Seq(Var("mcexpr_target"))), "field_name")
                , loadField("field_name", SetLit(Seq(Var("field"))), "name")
                , `if`(And(Eq(SetLit(Seq(Var("field_name"))), SetLit(Seq(Var("mcexpr_target_field_name")))),
                         Eq(SetLit(Seq(Var("class"))), SetLit(Seq(Var("mcexpr_target_target_type")))))
                      , assignField(SetLit(Seq(Var("mcexpr"))), "target", SetLit(Seq(Var("mcexpr_target_target"))))
                      , stmtSeq()))
                , stmtSeq())
      ))
    // Remove the delegate field
    , assignField(SetLit(Seq(Var("class"))), "fields", Diff(SetVar("class_fields"), SetLit(Seq(Var("field")))))
    )

    def executeRefactoring(name: String, initialMems: List[SMem], refactoring: Statement): Unit = {
      import testing._

      import scalaz.concurrent.Task
      import scalaz.stream._

      val tg = new WhiteBoxTestGenerator(FullClassModel.allDefsWithKeys, beta=1, delta=1, kappa=2)
      val task: Task[Unit] = tg.generateTestsE(Set(initialMems : _*), refactoring).map(_.toString).to(io.stdOutLines).run
      println("-" * 20)
      println(s"Starting execution of $name")
      println("-" * 20)
      task.run
      println("-" * 20)
      println(s"Finished execution of $name")
      println("-" * 20)
    }

    def main(args : Array[String]): Unit = {
      executeRefactoring("Rename-Field", List(renameFieldInput), renameFieldAst)
      //executeRefactoring("Rename-Method", List(renameMethodInput), renameMethod)
      //executeRefactoring("Extract-Super-Class", List(extractSuperclassInput), extractSuperclassAst)
      //executeRefactoring("Replace-Delegation-with-Inheritance", List(replaceDelegationWithInheritanceInput), replaceDelegationWithInheritanceAst)
    }

}
