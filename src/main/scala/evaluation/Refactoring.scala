package evaluation

import syntax.ast._

object Refactoring {


  def macro__get__supers(c : SetExpr, supers: Vars): Statement = StmtSeq(
      AssignVar("__cclass", SetLit(Var("oclass")))
    , AssignVar(supers, SetLit())
    , Fix(SetVar("__cclass"), StmtSeq(
            If(Not(Eq(SetVar("__cclass"), SetLit())) -> StmtSeq(
                 LoadField("__cclass_super", SetLit(Var("__cclass")), "super")
                   , AssignVar(supers, Union(SetVar(supers), SetVar("__cclass_super")))
                   , AssignVar("__cclass", SetVar("__cclass_super"))
            ))
    ))
   )

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
                                                 Map("classes" -> Union(SetSymbol(packageClassesId), SetLit(Symbol(classId)))),
                                                 Map[Fields, SetExpr]()),
                                  classId ->
                                    ConcreteDesc(Class("Class"),
                                                 Map("fields" -> Union(SetSymbol(classFieldsId), SetLit(Symbol(oldFieldId))),
                                                     "methods" -> SetSymbol(classMethodsId))
                                                , Map("name" -> SetLit(Symbol(classNameId)),
                                                      "super" -> SetSymbol(classSuperId))),
                                   oldFieldId -> AbstractDesc(Class("Field"), SetLit()),
                                   newFieldId -> AbstractDesc(Class("Field"), SetLit())),
                              Set(QSpatial(SetSymbol(packageClassesId), Class("Class"), SetLit()),
                                  QSpatial(SetSymbol(classFieldsId), Class("Field"), SetLit()),
                                  QSpatial(SetSymbol(classMethodsId), Class("Method"), SetLit())),
                              Set())
        SMem(inputStack, inputHeap)
  }

  // Input:: package: Package, class: Class, old_field : Field, new_field : Field
  val renameField: Statement = StmtSeq(
    LoadField("class_fields", SetLit(Var("class")), "fields")
  , AssignField(SetLit(Var("class")), "fields", Union(Diff(SetVar("class_fields"), SetLit(Var("old_field"))), SetLit(Var("new_field"))))
  , For("faexpr", MatchStar(SetLit(Var("package")), Class("FieldAccessExpr")), StmtSeq(
            LoadField("faexpr_field_name", SetLit(Var("faexpr")), "field_name")
          , LoadField("old_field_name", SetLit(Var("old_field")), "name")
          , LoadField("faexpr_target", SetLit(Var("faexpr")), "target")
          , LoadField("faexpr_target_type", SetLit(Var("faexpr_target")), "type")
          , macro__get__supers(SetLit(Var("faexpr_target_type")), "faet_supers")
          , AssignVar("faet_supers_or_self", Union(SetVar("faet_supers"), SetLit(Var("faexpr_target_type"))))
          , If(And(Eq(SetLit(Var("faexpr_field_name")), SetLit(Var("old_field_name"))),
                   SetMem(Var("class"), SetVar("faet_supers_or_self"))) -> StmtSeq(
                 LoadField("new_field_name", SetLit(Var("new_field")), "name")
               , AssignField(SetLit(Var("faexpr")), "name", SetLit(Var("new_field_name")))
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
                                                 Map("classes" -> Union(SetSymbol(packageClassesId), SetLit(Symbol(classId)))),
                                                 Map[Fields, SetExpr]()),
                                  classId ->
                                    ConcreteDesc(Class("Class"),
                                                 Map("fields" -> SetSymbol(classFieldsId),
                                                     "methods" -> Union(SetSymbol(classMethodsId), SetLit(Symbol(oldMethodId))))
                                                , Map("name" -> SetLit(Symbol(classNameId)),
                                                      "super" -> SetSymbol(classSuperId))),
                                   oldMethodId -> AbstractDesc(Class("Field"), SetLit()),
                                   newMethodId -> AbstractDesc(Class("Field"), SetLit())),
                              Set(QSpatial(SetSymbol(packageClassesId), Class("Class"), SetLit()),
                                  QSpatial(SetSymbol(classFieldsId), Class("Field"), SetLit()),
                                  QSpatial(SetSymbol(classMethodsId), Class("Method"), SetLit())),
                              Set())
        SMem(inputStack, inputHeap)
  }

  // Input:: package: Package, class: Class, old_method : Method, new_method : Method
  //Assumes overloading is not allowed (but overriding is), things are semantically checked, and that the transformation is applicable
  val renameMethod: Statement  = StmtSeq(
     LoadField("class_methods", SetLit(Var("class")), "methods")
   , AssignField(SetLit(Var("class")), "methods", Union(Diff(SetVar("class_methods"), SetLit(Var("old_method"))), SetLit(Var("new_method"))))
   , For("oclass", MatchStar(SetLit(Var("package")), Class("Class")), StmtSeq(
           macro__get__supers(SetLit(Var("oclass")), "supers")
         , If(SetMem(Var("class"), SetVar("supers")) -> StmtSeq(
                 LoadField("oclass_methods", SetLit(Var("oclass")), "methods")
                , For("m", MSet(SetVar("oclass_methods")), StmtSeq(
                          LoadField("m_name", SetLit(Var("m")), "name")
                        , LoadField("old_method_name", SetLit(Var("old_method")), "name")
                        , If(Eq(SetVar("m_name"), SetVar("old_method_name")) -> StmtSeq(
                               LoadField("new_method_name", SetLit(Var("new_method")), "name")
                             , AssignField(SetLit(Var("m")), "name", SetLit(Var("new_method_name")))
                            ))
                     ))
             ))
        ))
   , For("mcexpr", MatchStar(SetLit(Var("package")), Class("MethodCallExpr")), StmtSeq(
          LoadField("mcexpr_method_name", SetLit(Var("mcexpr")), "method_name")
        , LoadField("old_method_name", SetLit(Var("old_method")), "name")
        , LoadField("mcexpr_target", SetLit(Var("mcexpr")), "target")
        , LoadField("mcexpr_target_type", SetLit(Var("mcexpr_target")), "type")
        , macro__get__supers(SetLit(Var("mcexpr_target_type")), "mcet_supers")
        , AssignVar("mcet_supers_or_self", Union(SetVar("mcet_supers"), SetLit(Var("mcexpr_target_type"))))
        , If(And(Eq(SetLit(Var("mcexpr_method_name")), SetLit(Var("old_method_name"))),
                SetMem(Var("class"), SetVar("mcet_supers_or_self"))) -> StmtSeq(
                  LoadField("new_method_name", SetLit(Var("new_method")), "name")
                , AssignField(SetLit(Var("mcexpr")), "name", SetLit(Var("new_method_name")))
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
                                                  Map("classes" -> Union(SetSymbol(packageClassesId), SetLit(Symbol(class1Id), Symbol(class2Id)))),
                                                  Map[Fields, SetExpr]()),
                                    class1Id -> AbstractDesc(Class("Class"), SetLit()),
                                    class2Id -> AbstractDesc(Class("Class"), SetLit())),
                               Set(QSpatial(SetSymbol(packageClassesId), Class("Class"), SetLit())),
                               Set())
         SMem(inputStack, inputHeap)
   }

  // Input:: class1 : Class, class2 : Class, sc_name : String
  val extractSuperclass: Statement = StmtSeq(
      New("sclass", Class("Class"))
    , LoadField("package_classes", SetLit(Var("package")), "classes")
    , AssignField(SetLit(Var("package")), "classes", Union(SetVar("package_classes"), SetLit(Var("sclass"))))
    , AssignField(SetLit(Var("class1")), "super", SetLit(Var("sclass")))
    , AssignField(SetLit(Var("class2")), "super", SetLit(Var("sclass")))
    , AssignField(SetLit(Var("sclass")), "name", SetLit(Var("sc_name")))
    // Pull up relevant fields
    , AssignVar("new_sclass_fields", SetLit())
    , AssignVar("new_class1_fields", SetLit())
    , AssignVar("new_class2_fields", SetLit())
    , LoadField("class1_fields", SetLit(Var("class1")), "fields")
    , LoadField("class2_fields", SetLit(Var("class2")), "fields")
    , For("c1f", MSet(SetVar("class1_fields")), StmtSeq(
            For("c2f", MSet(SetVar("class2_fields")), StmtSeq(
                     LoadField("c1f_name", SetLit(Var("c1f")), "name")
                   , LoadField("c2f_name", SetLit(Var("c2f")), "name")
                   , If(Eq(SetLit(Var("c1f_name")), SetLit(Var("c2f_name"))) -> StmtSeq(
                           New("scf", Class("Field"))
                         , AssignField(SetLit(Var("scf")), "name", SetLit(Var("c1f_name")))
                         , LoadField("c1f_type", SetLit(Var("c1f")), "type")
                         , AssignField(SetLit(Var("scf")), "type", SetLit(Var("c1f_type")))
                         , AssignVar("new_sclass_fields", Union(SetVar("new_sclass_fields"), SetLit(Var("scf"))))
                        )
                        , Not(Eq(SetLit(Var("c1f_name")), SetLit(Var("c2f_name")))) -> StmtSeq(
                             AssignVar("new_class1_fields", Union(SetVar("new_class1_fields"), SetLit(Var("c1f"))))
                           , AssignVar("new_class2_fields", Union(SetVar("new_class2_fields"), SetLit(Var("c2f"))))
                        ))
                ))
         ))
   , AssignField(SetLit(Var("class1")), "fields", SetVar("new_class1_fields"))
   , AssignField(SetLit(Var("class2")), "fields", SetVar("new_class2_fields"))
   , AssignField(SetLit(Var("sclass")), "fields", SetVar("new_sclass_fields"))
   // Pull up relevant methods
   , AssignVar("new_sclass_methods", SetLit())
   , AssignVar("new_class1_methods", SetLit())
   , AssignVar("new_class2_methods", SetLit())
   , LoadField("class1_methods", SetLit(Var("class1")), "methods")
   , LoadField("class2_methods", SetLit(Var("class2")), "methods")
   , For("c1m", MSet(SetVar("class1_methods")), StmtSeq(
        For("c2m", MSet(SetVar("class2_methods")), StmtSeq(
                  LoadField("c1m_name", SetLit(Var("c1m")), "name")
                , LoadField("c2m_name", SetLit(Var("c2m")), "name")
                , If(Eq(SetLit(Var("c1m_name")), SetLit(Var("c2m_name"))) -> StmtSeq(
                        New("scm", Class("Field"))
                        , AssignField(SetLit(Var("scm")), "name", SetLit(Var("c1m_name")))
                        , LoadField("c1m_type", SetLit(Var("c1m")), "type")
                        , AssignField(SetLit(Var("scm")), "type", SetLit(Var("c1m_type")))
                        , LoadField("c1m_params", SetLit(Var("c1m")), "params")
                          // Copy parameter list
                        , If(Not(Eq(SetLit(Var("c1m_params")), SetLit())) -> StmtSeq(
                                New("scm_params", Class("Param"))
                              , LoadField("c1m_params_name", SetLit(Var("c1m_params")), "name")
                              , AssignField(SetLit(Var("scm_params")), "name", SetLit(Var("c1m_params_name")))
                              , LoadField("c1m_params_type", SetLit(Var("c1m_params")), "type")
                              , AssignField(SetLit(Var("scm_params")), "type", SetLit(Var("c1m_params_type")))
                              , AssignVar("scmp_curr", SetLit(Var("scm_params")))
                              , LoadField("c1mp_next", SetLit(Var("c1m_params")), "next")
                              , Fix(SetVar("c1mp_next"),
                                  If(Not(Eq(SetVar("c1mp_next"), SetLit())) -> StmtSeq(
                                      New("scmp_next", Class("Param"))
                                    , LoadField("c1mp_next_name", SetLit(Var("c1mp_next")), "name")
                                    , AssignField(SetLit(Var("scmp_next")), "name", SetLit(Var("c1mp_next_name")))
                                    , LoadField("c1mp_next_type", SetLit(Var("c1mp_next")), "type")
                                    , AssignField(SetLit(Var("scmp_next")), "type", SetLit(Var("c1mp_next_type")))
                                    , AssignField(SetLit(Var("scmp_curr")), "next", SetLit(Var("scmp_next")))
                                    , AssignVar("scmp_curr", SetLit(Var("scmp_next")))
                                    , LoadField("c1mp_next_next", SetLit(Var("c1mp_next")), "next")
                                    , AssignVar("c1mp_next", SetVar("c1mp_next_next"))
                                    ))
                                )
                              , AssignField(SetLit(Var("scm")), "params", SetLit(Var("scm_params")))
                            ))
                        , AssignVar("new_sclass_methods", Union(SetVar("new_sclass_methods"), SetLit(Var("scm"))))
                    )
                    , Not(Eq(SetLit(Var("c1m_name")), SetLit(Var("c2m_name")))) -> StmtSeq(
                          AssignVar("new_class1_methods", Union(SetVar("new_class1_methods"), SetLit(Var("c1m"))))
                        , AssignVar("new_class2_methods", Union(SetVar("new_class2_methods"), SetLit(Var("c2m"))))
                    ))
            ))
        ))
   , AssignField(SetLit(Var("class1")), "methods", SetVar("new_class1_methods"))
   , AssignField(SetLit(Var("class2")), "methods", SetVar("new_class2_methods"))
   , AssignField(SetLit(Var("sclass")), "methods", SetVar("new_sclass_methods"))
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
                                                 Map("fields" -> Union(SetSymbol(classFieldsId), SetLit(Symbol(fieldId))),
                                                     "methods" -> SetSymbol(classMethodsId))
                                                , Map("name" -> SetLit(Symbol(classNameId)),
                                                      "super" -> SetSymbol(classSuperId))),
                                   fieldId -> AbstractDesc(Class("Field"), SetLit())),
                              Set(QSpatial(SetSymbol(classFieldsId), Class("Field"), SetLit()),
                                  QSpatial(SetSymbol(classMethodsId), Class("Method"), SetLit())),
                              Set())
        SMem(inputStack, inputHeap)
  }

  // Assumes that methods that have the same name as the delegate are delegated methods and that field is private
  // class: Class, field : Field
  val replaceDelegationWithInheritance : Statement = StmtSeq(
      LoadField("class_fields", SetLit(Var("class")), "fields")
    , LoadField("field_type", SetLit(Var("field")), "type")
    , AssignField(SetLit(Var("class")), "super", SetLit(Var("field_type")))
    // Remove all delegated methods
    , LoadField("field_type_methods", SetLit(Var("field_type")), "methods")
    , LoadField("class_methods", SetLit(Var("class")), "methods")
    , AssignVar("class_new_methods", SetLit())
    , For("ftm", MSet(SetVar("field_type_methods")), StmtSeq(
        For("cm", MSet(SetVar("class_methods")), StmtSeq(
              LoadField("ftm_name", SetLit(Var("ftm")), "name")
            , LoadField("cm_name", SetLit(Var("cm")), "name")
            , If(Not(Eq(SetLit(Var("ftm_name")), SetLit(Var("cm_name")))) -> StmtSeq(
                AssignVar("class_new_methods", Union(SetVar("class_new_methods"), SetLit(Var("cm"))))
              ))
          ))
      ))
    , AssignField(SetLit(Var("class")), "methods", SetVar("class_new_methods"))
    // Replace other delegations with calls to the object itself
    , For("mcexpr", MatchStar(SetLit(Var("class")), Class("MethodCallExpr")), StmtSeq(
          LoadField("mcexpr_target", SetLit(Var("mcexpr")), "target")
        , If(ClassMem(SetLit(Var("mcexpr_target")), Class("FieldAccessExpr")) -> StmtSeq(
              LoadField("mcexpr_target_target", SetLit(Var("mcexpr_target")), "target")
            , LoadField("mcexpr_target_target_type", SetLit(Var("mcexpr_target_target")), "type")
            , LoadField("mcexpr_target_field_name", SetLit(Var("mcexpr_target")), "field_name")
            , LoadField("field_name", SetLit(Var("field")), "name")
            , If(And(Eq(SetLit(Var("field_name")), SetLit(Var("mcexpr_target_field_name"))),
                     Eq(SetLit(Var("class")), SetLit(Var("mcexpr_target_target_type")))) -> StmtSeq(
                         AssignField(SetLit(Var("mcexpr")), "target", SetLit(Var("mcexpr_target_target")))
                       ))
          ))
      ))
    // Remove the delegate field
    , AssignField(SetLit(Var("class")), "fields", Diff(SetVar("class_fields"), SetLit(Var("field"))))
    )

    def executeRefactoring(name: String, initialMems: List[SMem], refactoring: Statement, p: scalaz.\/[String, SMem] => Boolean = (_ => true)): Unit = {
      import syntax.PrettyPrinter
      import semantics._
      import scalaz._, Scalaz._, scalaz.stream._
      import scalaz.concurrent.Task

      val symex = new SymbolicExecutor(FullClassModel.allDefsWithKeys, kappa = 2, beta = 5, delta = 7)
      val task: Task[Unit] = symex.execute(Process(initialMems : _*).map(_.right), refactoring).filter(p).map(path => path.fold(identity, mem => {
        val nmem: SMem = SetNormalizer.normalize(mem.heap.pure)(mem).cata(_.asInstanceOf[SMem], mem)
        s"Resulting memory: ${PrettyPrinter.pretty(nmem)}"})).to(io.stdOutLines).run
      println("-" * 20)
      println(s"Starting execution of $name")
      println("-" * 20)
      task.run
      println("-" * 20)
      println(s"Finished execution of $name")
      println("-" * 20)
    }

    def main(args : Array[String]): Unit = {
      //executeRefactoring("Rename-Field", List(renameFieldInput), renameField, _.isRight)
      //executeRefactoring("Rename-Method", List(renameMethodInput), renameMethod, _.isRight)
      //executeRefactoring("Extract-Super-Class", List(extractSuperclassInput), extractSuperclass, _.isRight)
      executeRefactoring("Replace-Delegation-with-Inheritance", List(replaceDelegationWithInheritanceInput), replaceDelegationWithInheritance)
    }

}
