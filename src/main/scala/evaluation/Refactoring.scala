import syntax.ast._

object Refactoring {

  val renameField: Statement = StmtSeq(
    LoadField("class_fields", SetLit(Var("class")), "fields")
  , AssignField(SetLit(Var("class")), "class_fields", Union(Diff(SetVar("class_fields"), SetLit(Var("old_field"))), SetLit(Var("new_field"))))
  , For("faexpr", MatchStar(SetLit(Var("package")), Class("FieldAccessExpr")), StmtSeq(
            LoadField("faexpr_field_name", SetLit(Var("faexpr")), "field_name")
          , LoadField("old_field_name", SetLit(Var("old_field")), "name")
          , LoadField("faexpr_target", SetLit(Var("faexpr")), "target")
          , LoadField("faexpr_target_type", SetLit(Var("faexpr_target")), "type")
          , If(And(Eq(SetLit(Var("faexpr_field_name")), SetLit(Var("old_field_name"))),
                   Eq(SetLit(Var("faexpr_target_type")), SetLit(Var("class")))) -> StmtSeq(
                 LoadField("new_field_name", SetLit(Var("new_field")), "name")
               , AssignField(SetLit(Var("faexpr")), "name", SetLit(Var("new_field_name")))
             ))
      ))
  )

  val renameMethod: Statement  = StmtSeq(
    LoadField("class_methods", SetLit(Var("class")), "methods")
    , AssignField(SetLit(Var("class")), "class_methods", Union(Diff(SetVar("class_methods"), SetLit(Var("old_method"))), SetLit(Var("new_method"))))
      // TODO Add rename method refactoring
    )
)

}
