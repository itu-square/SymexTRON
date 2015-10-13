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

  // Input:: package: Package, class: Class, old_field : Field, new_field : Field
  val renameField: Statement = StmtSeq(
    LoadField("class_fields", SetLit(Var("class")), "fields")
  , AssignField(SetLit(Var("class")), "class_fields", Union(Diff(SetVar("class_fields"), SetLit(Var("old_field"))), SetLit(Var("new_field"))))
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

  // Input:: package: Package, class: Class, old_method : Method, new_method : Method
  //Assumes overloading is not allowed (but overriding is), things are semantically checked, and that the transformation is applicable
  val renameMethod: Statement  = StmtSeq(
     LoadField("class_methods", SetLit(Var("class")), "methods")
   , AssignField(SetLit(Var("class")), "class_methods", Union(Diff(SetVar("class_methods"), SetLit(Var("old_method"))), SetLit(Var("new_method"))))
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

  // Input:: class1 : Class, class2 : Class, sc_name : String
  val extractSuperclass: Statement = StmtSeq(
      New("sclass", Class("Class"))
    , AssignField(SetLit(Var("class1")), "super", SetLit(Var("sclass")))
    , AssignField(SetLit(Var("class2")), "super", SetLit(Var("sclass")))
    , AssignField(SetLit(Var("sclass")), "name", SetLit(Var("scname")))
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


}
