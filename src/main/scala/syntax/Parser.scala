package syntax

import syntax.ast._
import com.codecommit.gll._

object Parser extends RegexParsers {

  override val whitespace = (
      """(\s|/\*([^*]|\*[^/])*\*/)+""".r
  )

  lazy val pSetExpr: Parser[SetExpr] = (
      pSetVar ^^ { SetVar(_) }
    | pVar ^^ (v => SetLit(Var(v)))
    | "{" ~> pVar.*(",") <~ "}" ^^ (vars => SetLit(vars.map(Var(_)) :_*))
    | (pSetExpr <~ pUnionOp) ~ pSetExpr ^^ { Union(_,_) }
    | (pSetExpr <~ pISectOp) ~ pSetExpr ^^ { ISect(_,_) }
    | (pSetExpr <~ pDiffOp)  ~ pSetExpr ^^ { Diff(_,_) }
    | "(" ~> pSetExpr <~ ")"
  )

  lazy val pUnionOp: Parser[String] = "union" | "∪"
  lazy val pISectOp: Parser[String] = "intersect" | "∩"
  lazy val pDiffOp:  Parser[String] = "diff" | "∖"

  lazy val pBoolExpr:  Parser[BoolExpr] = (
      (pSetExpr <~ pSetSubEqOp) ~ pSetExpr  ^^ { SetSubEq(_,_) }
    | (pSetExpr <~ pSetSubOp)   ~ pSetExpr  ^^ { SetSub(_,_)   }
    | (pVar <~ pSetMemOp)       ~ pSetExpr  ^^ { (v, e) => SetMem(Var(v),e) }
    | (pSetExpr <~ pClassMemOp) ~ pClass    ^^ { ClassMem(_,_) }
    | (pSetExpr <~ pEqOp)       ~ pSetExpr  ^^ { Eq(_,_) }
    | (pBoolExpr <~ pAndOp)     ~ pBoolExpr ^^ { And(_,_) }
    | (pBoolExpr <~ pOrOp)      ~ pBoolExpr ^^ { (b1, b2) => Not(And(Not(b1),Not(b2))) }
    | pNotOp ~> pBoolExpr                   ^^ { Not(_) }
    | "true" ^^^ { And() }
    | "(" ~> pBoolExpr <~ ")"
  )

  lazy val pSetSubEqOp = "subset=" | "⊆"
  lazy val pSetSubOp   = "subset" | "⊂"
  lazy val pSetMemOp   = "mem"    | "∈"
  lazy val pClassMemOp = ":"
  lazy val pEqOp       = "="
  lazy val pAndOp      = "&" | "∧"
  lazy val pOrOp       = "|" | "∨"
  lazy val pNotOp      = "!" | "¬"

  lazy val pMatchExpr: Parser[MatchExpr] = (
      pSetExpr ^^ { MSet(_) }
    | (pSetExpr <~ "match") ~ pClass ^^ { Match(_,_) }
    | (pSetExpr <~ "match*") ~ pClass ^^ { MatchStar(_,_) }
  )

  lazy val pVar: Parser[String] = (
    """[a-z][a-z0-9]*""".r
  )

  lazy val pField: Parser[String] = (
    """[a-z][a-z0-9]*""".r
  )

  lazy val pSetVar: Parser[String] = (
    """[A-Z][A-Z0-9]*""".r
  )

  lazy val pClass: Parser[Class] = (
    """[A-Z][a-zA-Z]*""".r ^^ { Class(_) }
  )

  lazy val pStatement: Parser[Statement] = (
      "[" ~> pStatement.*(";") <~ "]" ^^ { ss => Statement.stmtSeq(ss :_*) }
    | ((pSetVar | pVar) <~ ":=") ~ pSetExpr ^^ { Statement.assignVar(_,_) }
    | ((pSetVar | pVar) <~ ":=") ~ (pSetExpr <~ ".") ~ pField ^^ { Statement.loadField(_,_,_) }
    | ((pSetExpr <~ ".") ~ pField <~ ":=") ~  pSetExpr ^^ { Statement.assignField(_,_,_) }
    | ((pSetVar | pVar) <~ ":=" <~ "new") ~ pClass ^^ { Statement.`new`(_,_) }
    | ("fix" ~> pSetExpr <~ "do") ~ pStatement ^^ { Statement.fix(_,_) }
    | ("foreach" ~> pVar <~ "in") ~ (pMatchExpr <~ "do") ~ pStatement ^^ { Statement.`for`(_,_,_) }
    | ("if" ~> ("|" ~> pGuardedStatement).* <~ "else") ~ pStatement ^^ { (gss, ds) => Statement.`if`(ds, gss :_*) }
  )

  lazy val pGuardedStatement: Parser[(BoolExpr, Statement)] =
    (pBoolExpr <~ pArrowOp) ~ pStatement ^^ { (_,_) }

  lazy val pArrowOp: Parser[String] =
    "->" | "→"

}
