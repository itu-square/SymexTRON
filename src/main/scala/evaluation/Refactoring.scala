package evaluation

import syntax._
import syntax.ast._
import Statement._

object Refactoring {


  def macro__get__supers(c : String, supers: Vars): Statement = Parser.pStatement(
    s"""[
       CCLASS := $c;
       $supers := {};
       fix CCLASS do [
          if
          | !(CCLASS = {}) -> [ CCLASS_SUPER := CCLASS.super;
                                $supers := $supers union CCLASS_SUPER;
                                CCLASS := CLASS_SUPER ]
          else []
       ]
    ] """).head match {
    case com.codecommit.gll.Success(r, _) => r
    case com.codecommit.gll.Failure(d, _) => throw new Exception(s"Parse error: $d")
  }

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

        val inputStack = Map("package" -> SetLit(Symbol(packageId)), "class" -> SetLit(Symbol(classId)),
                             "old_field" -> SetLit(Symbol(oldFieldId)), "new_field" -> SetLit(Symbol(newFieldId)))
        val inputHeap = SHeap(Map(packageId ->
                                    ConcreteDesc(Class("Package"),
                                                 Map("classes" -> Union(SetSymbol((Class("Class"), Many), packageClassesId), SetLit(Symbol(classId)))),
                                                 Map[Fields, SetExpr]()),
                                  classId ->
                                    ConcreteDesc(Class("Class"),
                                                 Map("fields" -> Union(SetSymbol((Class("Field"), Many), classFieldsId), SetLit(Symbol(oldFieldId))),
                                                     "methods" -> SetSymbol((Class("Method"), Many), classMethodsId))
                                                , Map("name" -> SetLit(Symbol(classNameId)),
                                                      "super" -> SetSymbol((Class("Class"), Opt), classSuperId))),
                                   oldFieldId -> AbstractDesc(Class("Field")),
                                   newFieldId -> AbstractDesc(Class("Field")),
                                   classNameId -> ConcreteDesc(Class("String"), Map(), Map())),
                              Set(QSpatial(SetSymbol((Class("Class"), Many),  packageClassesId), Class("Class")),
                                  QSpatial(SetSymbol((Class("Field"), Many),  classFieldsId), Class("Field")),
                                  QSpatial(SetSymbol((Class("Method"), Many), classMethodsId), Class("Method"))),
                              Set())
        SMem(inputStack, inputHeap)
  }

  // Input:: package: Package, class: Class, old_field : Field, new_field : Field
  val renameFieldAst: Statement = stmtSeq(
    loadField("class_fields", SetLit(Var("class")), "fields")
  , assignField(SetLit(Var("class")), "fields", Union(Diff(SetVar("class_fields"), SetLit(Var("old_field"))), SetLit(Var("new_field"))))
  , `for`("faexpr", MatchStar(SetLit(Var("package")), Class("FieldAccessExpr")), stmtSeq(
            loadField("faexpr_field_name", SetLit(Var("faexpr")), "field_name")
          , loadField("old_field_name", SetLit(Var("old_field")), "name")
          , loadField("faexpr_target", SetLit(Var("faexpr")), "target")
          , loadField("faexpr_target_type", SetLit(Var("faexpr_target")), "type")
          , macro__get__supers("faexpr_target_type", "FAET_SUPERS")
          , assignVar("faet_supers_or_self", Union(SetVar("FAET_SUPERS"), SetLit(Var("faexpr_target_type"))))
          , `if`(stmtSeq(), And(Eq(SetLit(Var("faexpr_field_name")), SetLit(Var("old_field_name"))),
                   SetMem(Var("class"), SetVar("faet_supers_or_self"))) -> stmtSeq(
                 loadField("new_field_name", SetLit(Var("new_field")), "name")
               , assignField(SetLit(Var("faexpr")), "name", SetLit(Var("new_field_name")))
             ))
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

        val inputStack = Map("package" -> SetLit(Symbol(packageId)), "class" -> SetLit(Symbol(classId)),
                             "old_method" -> SetLit(Symbol(oldMethodId)), "new_method" -> SetLit(Symbol(newMethodId)))
        val inputHeap = SHeap(Map(packageId ->
                                    ConcreteDesc(Class("Package"),
                                                 Map("classes" -> Union(SetSymbol((Class("Class"), Many), packageClassesId), SetLit(Symbol(classId)))),
                                                 Map[Fields, SetExpr]()),
                                  classId ->
                                    ConcreteDesc(Class("Class"),
                                                 Map("fields" -> SetSymbol((Class("Field"), Many) , classFieldsId),
                                                     "methods" -> Union(SetSymbol((Class("Method"), Many), classMethodsId), SetLit(Symbol(oldMethodId))))
                                                , Map("name" -> SetLit(Symbol(classNameId)),
                                                      "super" -> SetSymbol((Class("Class"), Opt), classSuperId))),
                                   oldMethodId -> AbstractDesc(Class("Method")),
                                   newMethodId -> AbstractDesc(Class("Method"))),
                              Set(QSpatial(SetSymbol((Class("Class"), Many), packageClassesId), Class("Class")),
                                  QSpatial(SetSymbol((Class("Field"), Many), classFieldsId), Class("Field")),
                                  QSpatial(SetSymbol((Class("Method"), Many), classMethodsId), Class("Method"))),
                              Set())
        SMem(inputStack, inputHeap)
  }

  // Input:: package: Package, class: Class, old_method : Method, new_method : Method
  //Assumes overloading is not allowed (but overriding is), things are semantically checked, and that the transformation is applicable
  val renameMethodAst: Statement  = stmtSeq(
     loadField("class_methods", SetLit(Var("class")), "methods")
   , assignField(SetLit(Var("class")), "methods", Union(Diff(SetVar("class_methods"), SetLit(Var("old_method"))), SetLit(Var("new_method"))))
   , `for`("oclass", MatchStar(SetLit(Var("package")), Class("Class")), stmtSeq(
           macro__get__supers("oclass", "SUPERS")
         , `if`(stmtSeq(), SetMem(Var("class"), SetVar("SUPERS")) -> stmtSeq(
                 loadField("oclass_methods", SetLit(Var("oclass")), "methods")
                , `for`("m", MSet(SetVar("oclass_methods")), stmtSeq(
                          loadField("m_name", SetLit(Var("m")), "name")
                        , loadField("old_method_name", SetLit(Var("old_method")), "name")
                        , `if`(stmtSeq(), Eq(SetVar("m_name"), SetVar("old_method_name")) -> stmtSeq(
                               loadField("new_method_name", SetLit(Var("new_method")), "name")
                             , assignField(SetLit(Var("m")), "name", SetLit(Var("new_method_name")))
                            ))
                     ))
             ))
        ))
   , `for`("mcexpr", MatchStar(SetLit(Var("package")), Class("MethodCallExpr")), stmtSeq(
          loadField("mcexpr_method_name", SetLit(Var("mcexpr")), "method_name")
        , loadField("old_method_name", SetLit(Var("old_method")), "name")
        , loadField("mcexpr_target", SetLit(Var("mcexpr")), "target")
        , loadField("mcexpr_target_type", SetLit(Var("mcexpr_target")), "type")
        , macro__get__supers("mcexpr_target_type", "MCET_SUPERS")
        , assignVar("mcet_supers_or_self", Union(SetVar("MCET_SUPERS"), SetLit(Var("mcexpr_target_type"))))
        , `if`(stmtSeq(), And(Eq(SetLit(Var("mcexpr_method_name")), SetLit(Var("old_method_name"))),
                SetMem(Var("class"), SetVar("mcet_supers_or_self"))) -> stmtSeq(
                  loadField("new_method_name", SetLit(Var("new_method")), "name")
                , assignField(SetLit(Var("mcexpr")), "name", SetLit(Var("new_method_name")))
            ))
        ))
   )
   val extractSuperclassInput: SMem = {
         val packageId        = -1
         val class1Id         = -2
         val class2Id         = -3
         val scnameId         = -4
         val packageClassesId = -5

         val inputStack = Map("package" -> SetLit(Symbol(packageId)), "class1" -> SetLit(Symbol(class1Id)),
                              "class2" -> SetLit(Symbol(class2Id)), "sc_name" -> SetLit(Symbol(scnameId)))
         val inputHeap = SHeap(Map(packageId ->
                                     ConcreteDesc(Class("Package"),
                                                  Map("classes" -> Union(SetSymbol((Class("Class"), Many), packageClassesId), SetLit(Symbol(class1Id), Symbol(class2Id)))),
                                                  Map[Fields, SetExpr]()),
                                    class1Id -> AbstractDesc(Class("Class")),
                                    class2Id -> AbstractDesc(Class("Class"))),
                               Set(QSpatial(SetSymbol((Class("Class"), Many), packageClassesId), Class("Class"))),
                               Set())
         SMem(inputStack, inputHeap)
   }

  // Input:: class1 : Class, class2 : Class, sc_name : String
  val extractSuperclassAst: Statement = stmtSeq(
      `new`("sclass", Class("Class"))
    , loadField("package_classes", SetLit(Var("package")), "classes")
    , assignField(SetLit(Var("package")), "classes", Union(SetVar("package_classes"), SetLit(Var("sclass"))))
    , assignField(SetLit(Var("class1")), "super", SetLit(Var("sclass")))
    , assignField(SetLit(Var("class2")), "super", SetLit(Var("sclass")))
    , assignField(SetLit(Var("sclass")), "name", SetLit(Var("sc_name")))
    // Pull up relevant fields
    , assignVar("new_sclass_fields", SetLit())
    , assignVar("new_class1_fields", SetLit())
    , assignVar("new_class2_fields", SetLit())
    , loadField("class1_fields", SetLit(Var("class1")), "fields")
    , loadField("class2_fields", SetLit(Var("class2")), "fields")
    , `for`("c1f", MSet(SetVar("class1_fields")), stmtSeq(
            `for`("c2f", MSet(SetVar("class2_fields")), stmtSeq(
                     loadField("c1f_name", SetLit(Var("c1f")), "name")
                   , loadField("c2f_name", SetLit(Var("c2f")), "name")
                   , `if`(stmtSeq(
                            assignVar("new_class1_fields", Union(SetVar("new_class1_fields"), SetLit(Var("c1f"))))
                          , assignVar("new_class2_fields", Union(SetVar("new_class2_fields"), SetLit(Var("c2f"))))
                         ), Eq(SetLit(Var("c1f_name")), SetLit(Var("c2f_name"))) -> stmtSeq(
                          `new`("scf", Class("Field"))
                         , assignField(SetLit(Var("scf")), "name", SetLit(Var("c1f_name")))
                         , loadField("c1f_type", SetLit(Var("c1f")), "type")
                         , assignField(SetLit(Var("scf")), "type", SetLit(Var("c1f_type")))
                         , assignVar("new_sclass_fields", Union(SetVar("new_sclass_fields"), SetLit(Var("scf"))))
                        ))
                ))
         ))
   , assignField(SetLit(Var("class1")), "fields", SetVar("new_class1_fields"))
   , assignField(SetLit(Var("class2")), "fields", SetVar("new_class2_fields"))
   , assignField(SetLit(Var("sclass")), "fields", SetVar("new_sclass_fields"))
   // Pull up relevant methods
   , assignVar("new_sclass_methods", SetLit())
   , assignVar("new_class1_methods", SetLit())
   , assignVar("new_class2_methods", SetLit())
   , loadField("class1_methods", SetLit(Var("class1")), "methods")
   , loadField("class2_methods", SetLit(Var("class2")), "methods")
   , `for`("c1m", MSet(SetVar("class1_methods")), stmtSeq(
        `for`("c2m", MSet(SetVar("class2_methods")), stmtSeq(
                  loadField("c1m_name", SetLit(Var("c1m")), "name")
                , loadField("c2m_name", SetLit(Var("c2m")), "name")
                , `if`(stmtSeq(
                        assignVar("new_class1_methods", Union(SetVar("new_class1_methods"), SetLit(Var("c1m"))))
                      , assignVar("new_class2_methods", Union(SetVar("new_class2_methods"), SetLit(Var("c2m"))))),
                      Eq(SetLit(Var("c1m_name")), SetLit(Var("c2m_name"))) -> stmtSeq(
                        `new`("scm", Class("Field"))
                        , assignField(SetLit(Var("scm")), "name", SetLit(Var("c1m_name")))
                        , loadField("c1m_type", SetLit(Var("c1m")), "type")
                        , assignField(SetLit(Var("scm")), "type", SetLit(Var("c1m_type")))
                        , loadField("c1m_params", SetLit(Var("c1m")), "params")
                          // Copy parameter list
                        , `if`(stmtSeq(), Not(Eq(SetLit(Var("c1m_params")), SetLit())) -> stmtSeq(
                                `new`("scm_params", Class("Param"))
                              , loadField("c1m_params_name", SetLit(Var("c1m_params")), "name")
                              , assignField(SetLit(Var("scm_params")), "name", SetLit(Var("c1m_params_name")))
                              , loadField("c1m_params_type", SetLit(Var("c1m_params")), "type")
                              , assignField(SetLit(Var("scm_params")), "type", SetLit(Var("c1m_params_type")))
                              , assignVar("scmp_curr", SetLit(Var("scm_params")))
                              , loadField("c1mp_next", SetLit(Var("c1m_params")), "next")
                              , `fix`(SetVar("c1mp_next"),
                                  `if`(stmtSeq(), Not(Eq(SetVar("c1mp_next"), SetLit())) -> stmtSeq(
                                      `new`("scmp_next", Class("Param"))
                                    , loadField("c1mp_next_name", SetLit(Var("c1mp_next")), "name")
                                    , assignField(SetLit(Var("scmp_next")), "name", SetLit(Var("c1mp_next_name")))
                                    , loadField("c1mp_next_type", SetLit(Var("c1mp_next")), "type")
                                    , assignField(SetLit(Var("scmp_next")), "type", SetLit(Var("c1mp_next_type")))
                                    , assignField(SetLit(Var("scmp_curr")), "next", SetLit(Var("scmp_next")))
                                    , assignVar("scmp_curr", SetLit(Var("scmp_next")))
                                    , loadField("c1mp_next_next", SetLit(Var("c1mp_next")), "next")
                                    , assignVar("c1mp_next", SetVar("c1mp_next_next"))
                                    ))
                                )
                              , assignField(SetLit(Var("scm")), "params", SetLit(Var("scm_params")))
                            ))
                        , assignVar("new_sclass_methods", Union(SetVar("new_sclass_methods"), SetLit(Var("scm"))))
                    ))
            ))
        ))
   , assignField(SetLit(Var("class1")), "methods", SetVar("new_class1_methods"))
   , assignField(SetLit(Var("class2")), "methods", SetVar("new_class2_methods"))
   , assignField(SetLit(Var("sclass")), "methods", SetVar("new_sclass_methods"))
  )

  val replaceDelegationWithInheritanceInput: SMem = {
        val classId          = -1
        val fieldId          = -2
        val classFieldsId    = -3
        val classMethodsId   = -4
        val classNameId      = -5
        val classSuperId     = -6

        val inputStack = Map("class" -> SetLit(Symbol(classId)),
                             "field" -> SetLit(Symbol(fieldId)))
        val inputHeap = SHeap(Map(classId ->
                                    ConcreteDesc(Class("Class"),
                                                 Map("fields" -> Union(SetSymbol((Class("Field"), Many), classFieldsId), SetLit(Symbol(fieldId))),
                                                     "methods" -> SetSymbol((Class("Method"), Many), classMethodsId))
                                                , Map("name" -> SetLit(Symbol(classNameId)),
                                                      "super" -> SetSymbol((Class("Class"), Opt), classSuperId))),
                                   fieldId -> AbstractDesc(Class("Field")),
                                   classNameId -> ConcreteDesc(Class("String"), Map(), Map())),
                              Set(QSpatial(SetSymbol((Class("Field"), Many), classFieldsId), Class("Field")),
                                  QSpatial(SetSymbol((Class("Method"), Many), classMethodsId), Class("Method"))),
                              Set())
        SMem(inputStack, inputHeap)
  }

  // Assumes that methods that have the same name as the delegate are delegated methods and that field is private
  // class: Class, field : Field
  val replaceDelegationWithInheritanceAst : Statement = stmtSeq(
      loadField("class_fields", SetLit(Var("class")), "fields")
    , loadField("field_type", SetLit(Var("field")), "type")
    , assignField(SetLit(Var("class")), "super", SetLit(Var("field_type")))
    // Remove all delegated methods
    , loadField("field_type_methods", SetLit(Var("field_type")), "methods")
    , loadField("class_methods", SetLit(Var("class")), "methods")
    , assignVar("class_new_methods", SetLit())
    , `for`("ftm", MSet(SetVar("field_type_methods")), stmtSeq(
        `for`("cm", MSet(SetVar("class_methods")), stmtSeq(
              loadField("ftm_name", SetLit(Var("ftm")), "name")
            , loadField("cm_name", SetLit(Var("cm")), "name")
            , `if`(stmtSeq(), Not(Eq(SetLit(Var("ftm_name")), SetLit(Var("cm_name")))) -> stmtSeq(
                assignVar("class_new_methods", Union(SetVar("class_new_methods"), SetLit(Var("cm"))))
              ))
          ))
      ))
    , assignField(SetLit(Var("class")), "methods", SetVar("class_new_methods"))
    // Replace other delegations with calls to the object itself
    , `for`("mcexpr", MatchStar(SetLit(Var("class")), Class("MethodCallExpr")), stmtSeq(
          loadField("mcexpr_target", SetLit(Var("mcexpr")), "target")
        , `if`(stmtSeq(), ClassMem(Var("mcexpr_target"), Class("FieldAccessExpr")) -> stmtSeq(
              loadField("mcexpr_target_target", SetLit(Var("mcexpr_target")), "target")
            , loadField("mcexpr_target_target_type", SetLit(Var("mcexpr_target_target")), "type")
            , loadField("mcexpr_target_field_name", SetLit(Var("mcexpr_target")), "field_name")
            , loadField("field_name", SetLit(Var("field")), "name")
            , `if`(stmtSeq(), And(Eq(SetLit(Var("field_name")), SetLit(Var("mcexpr_target_field_name"))),
                     Eq(SetLit(Var("class")), SetLit(Var("mcexpr_target_target_type")))) -> stmtSeq(
                         assignField(SetLit(Var("mcexpr")), "target", SetLit(Var("mcexpr_target_target")))
                       ))
          ))
      ))
    // Remove the delegate field
    , assignField(SetLit(Var("class")), "fields", Diff(SetVar("class_fields"), SetLit(Var("field"))))
    )

    def executeRefactoring(name: String, initialMems: List[SMem], refactoring: Statement): Unit = {
      import testing._
      import scalaz._, Scalaz._, scalaz.stream._
      import scalaz.concurrent.Task

      val tg = new TestGenerator(FullClassModel.allDefsWithKeys, beta=1, delta=1, kappa=2)
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
