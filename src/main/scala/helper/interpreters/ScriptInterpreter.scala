package helper.interpreters

import scalaz.{Success => _,_}, Scalaz._

import smtlib.parser.Commands._
import smtlib.parser.Terms._
import smtlib.parser.CommandsResponses._
import smtlib.interpreters._


class ScriptInterpreter private (private val interpreter: ProcessInterpreter) {

  def interpret(s : Script): CommandResponse = {
    s.commands.foldLeft[CommandResponse](Success)((r, c) => r match {
      case _: SuccessfulResponse => interpreter.eval(c) match {
        case r:CommandResponse => r
        case r => print(r); throw new RuntimeException("")
      }
      case r => r
    })
  }

  def satStatus(c : CommandResponse): Option[Status] = c match {
    case CheckSatStatus(r) => r.some
    case _ => none
  }

  def getModel: Option[List[SExpr]] = interpreter.eval(GetModel()) match {
    case GetModelResponseSuccess(r) => r.some
    case _ => none
  }

  def free() {
    if (interpreter != null) interpreter.free()
  }
}

object ScriptInterpreter {
  def apply(interpreter: => ProcessInterpreter): ScriptInterpreter = {
    var itp: ProcessInterpreter = null
    try {
      itp = interpreter
      new ScriptInterpreter(itp)
    } catch {
      case t: Throwable => Option(itp).map(_.free()); throw t
    }
  }

}
