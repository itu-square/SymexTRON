package helper
package interpreters

import smtlib.interpreters._

object CVCInterpreter {

  val defaultArgs: Array[String] =
    Array("-q",
          "--produce-models",
          "--no-incremental",
          "--tear-down-incremental",
          "--dt-rewrite-error-sel",
          "--print-success",
          "--lang", "smt2.5")

  def build(args: Array[String] = defaultArgs) = {
    val executable = "cvc4"
    new CVC4Interpreter(executable, args)
  }
}
