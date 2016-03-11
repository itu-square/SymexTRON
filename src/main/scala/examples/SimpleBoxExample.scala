package examples

import semantics.domains._
import syntax.ast._

/**
  * Created by asal on 06/03/2016.
  */
trait SimpleBoxExample extends Example {

  override val classDefs: Set[ClassDefinition] = Shared.stdClassDefs ++ Set(
    ClassDefinition("IntBox", Map(), Map("unbox" -> (Class("Int"), Single)))
  )

  override val pres: Set[SMem] = {
    val stack = Map("x" -> SetLit(Seq(Symbol(-1))), "y" -> SetLit(Seq(Symbol(-2))))
    Set(
      SMem(stack, stack,
        SHeap.initial(Map(), Map(Symbol(-1) -> UnknownLoc(Class("IntBox"), SUnowned),
          Symbol(-2) -> UnknownLoc(Class("IntBox"), SUnowned)), Map(), Map(), Set()) )
    )
  }


}

object SimpleBoxSequentialLoadingExample extends SimpleBoxExample {
  import Statement._

  override val prog: Statement = stmtSeq(
      loadField("z", SetLit(Seq(Var("x"))), "unbox"),
      loadField("z", SetLit(Seq(Var("y"))), "unbox")
  )
}

object SimpleBoxBranchingLoadingExample extends SimpleBoxExample {
  import Statement._

  override val prog: Statement = `if`(Eq(SetLit(Seq(Var("x"))), SetLit(Seq(Var("y")))),
    loadField("z", SetLit(Seq(Var("y"))), "unbox")
    , loadField("z", SetLit(Seq(Var("x"))), "unbox")
  )
}

object SimpleBoxLoadingBranchingExample extends SimpleBoxExample {
  import Statement._

  override val prog: Statement = stmtSeq(
    loadField("z", SetLit(Seq(Var("x"))), "unbox"),
    `if`(Eq(SetLit(Seq(Var("x"))), SetLit(Seq(Var("y")))), stmtSeq(), stmtSeq())
  )
}
