package semantics

import scala.language.postfixOps
import scala.language.higherKinds

import syntax.ast._
import syntax.ast.CMem._
import syntax.ast.CHeap._
import scalaz._, Scalaz._
import scalaz.stream._, scalaz.concurrent.Task
import scala.concurrent.stm._
import helper._

class ConcreteExecutor(defs: Map[Class, ClassDefinition], _prog: Statement) {
  val prog = Statement.annotateUids(_prog)

  val progBranches = Statement.branches(prog)

  private val _stmtCoverage = TMap.empty[Integer, Boolean]
  private val _branchCoverage = TMap.empty[BranchPoint, Boolean]

  def stmtCoverage = Map(_stmtCoverage.single.toSeq: _*)
  def branchCoverage = Map(_branchCoverage.single.toSeq: _*)

  def execute(mem: CMem): Process[Task, String \/ CMem] = executeStmt(mem, prog)

  //TODO Check for type and ownership constraints
  private def executeStmt(mem: CMem, s: Statement): Process[Task, String \/ CMem] = {
    val uid = Statement._stmt_uid.getOption(s).get
    atomic { implicit txn =>
      _stmtCoverage.put(uid, true)
    }
    s match {
      case StmtSeq(_, ss @ _*) => {
        ss.toList.foldLeft[Process[Task, String \/ CMem]](Process.emit(mem.right)) {
          (pmem, s) =>
            for {
              memr <- pmem
              res <- memr.traverseU(mem => executeStmt(mem, s)).map(_.join)
            } yield res
        }
      }
      case AssignVar(_, x, e) => {
        (for {
          os <- evalExpr(e, mem.stack)
        } yield _cm_stack.modify(_.updated(x, os))(mem)) |> Process.emit
      }
      case LoadField(_, x, e, f) => (for {
        os <- evalExpr(e, mem.stack)
        o <- os.single.cata(_.right, s"Not a single object $os".left)
        os2 <- access(o, f, mem.heap)
      } yield _cm_stack.modify(_.updated(x, os2))(mem)) |> Process.emit
      case New(_, x, c) => (for {
        defc <- defs.get(c).cata(_.right, s"Unknown class $c".left)
        o = freshInstance
        ocs = defc.children.mapValues(_ => Set[Instances]())
        ors = defc.refs.mapValues(_ => Set[Instances]())
      } yield (_cm_stack.modify(_.updated(x, Set(o))) `andThen`
        _cm_heap.modify(
          _ch_typeenv.modify(_.updated(o, c)) `andThen`
            _ch_childenv.modify(_.updated(o, ocs)) `andThen`
            _ch_refenv.modify(_.updated(o, ors))
        ))(mem)) |> Process.emit
      case AssignField(_, e1, f, e2) => (for {
        os <- evalExpr(e1, mem.stack)
        o <- os.single.cata(_.right, s"Not a single object $os".left)
        os2 <- evalExpr(e2, mem.stack)
        h2 <- update(o, f, os2, mem.heap)
      } yield mem |> _cm_heap.set(h2)) |> Process.emit
      case If(_, ds, cs @ _*) => {
        val elseB = (cs.map(_._1).map(not).foldLeft[BoolExpr](True)(And(_,_)) , ds)
        val cs2 = elseB +: cs
        for {
          gs <- Process.emitAll(cs2.zipWithIndex.map(p => (p._1._1, p._1._2, p._2)))
          gr = evalBoolExpr(gs._1, mem.stack, mem.heap)
          res <- gr.traverseU(g => if (g) {
            _branchCoverage.updateValue(BranchPoint(uid, gs._3), _ => true)
            executeStmt(mem, gs._2)
          } else Process.empty).map(_.join)
        } yield res
      }
      case For(_, x, m, sb) => for {
        osr <- evalMatchExpr(m, mem.stack, mem.heap) |> Process.emit
        res <- osr.traverseU(os => {
          if (os.size == 0)
            _branchCoverage.updateValue(BranchPoint(uid, 0), _ => true)
          else
            _branchCoverage.updateValue(BranchPoint(uid, 1), _ => true)
          os.foldLeft[Process[Task, String \/ CMem]](
            Process.emit(mem.right)
          ) { (pmem, o) =>
              pmem.flatMap(_.traverseU(mem =>
                executeStmt(mem |>
                  _cm_stack.modify(_.updated(x, Set(o))), sb)).map(_.join))
            }
        }).map(_.join)
      } yield res
      case Fix(_, e, sb) => {
        def fix(mem: CMem): Process[Task, String \/ CMem] = for {
          nmemr <- executeStmt(mem, sb)
          res <- nmemr.flatMap(nmem => for {
            eeb <- evalExpr(e, mem.stack)
            eea <- evalExpr(e, nmem.stack)
          } yield (nmem, eeb, eea)).traverseU({ (nmem: CMem, eeb: Set[Instances], eea: Set[Instances]) =>
            if (eeb == eea) {
              _branchCoverage.updateValue(BranchPoint(uid, 0), _ => true)
              Process.emit(nmem.right)
            } else {
              _branchCoverage.updateValue(BranchPoint(uid, 1), _ => true)
              fix(nmem)
            }
          }.tupled).map(_.join)
        } yield res
        fix(mem)
      }
    }
  }

  private def access(o: Instances, f: Fields, h: CHeap): String \/ Set[Instances] = {
    if (defs.childfields.contains(f))
      h.childenv.get(o).flatMap(_.get(f))
        .cata(_.right, s"Child $f of object $o is not allocated".left)
    else if (defs.reffields.contains(f))
      h.refenv.get(o).flatMap(_.get(f))
        .cata(_.right, s"Reference $f of object $o is not allocated".left)
    else s"$f neither a child nor reference".left
  }

  // TODO implement more efficiently
  private def disown(h: CHeap, os2: Set[Instances]): CHeap = {
    h |> _ch_childenv.modify(_.mapValues(_.mapValues(os => os diff os2)))
  }

  private def update(o: Instances, f: Fields, os2: Set[Instances], h: CHeap): String \/ CHeap = {
    if (defs.childfields.contains(f))
      for {
        cs <- h.childenv.get(o).cata(_.right, s"Unknown object $o".left)
        _ <- cs.get(f).cata(_.right, s"Unknown child $f of object o".left)
      } yield h |>
        (disown _).un(os2) |>
        _ch_childenv.modify(_.updated(o, cs.updated(f, os2)))
    else if (defs.reffields.contains(f))
      for {
        rs <- h.refenv.get(o).cata(_.right, s"Unknown object $o".left)
        _ <- rs.get(f).cata(_.right, s"Unknown reference $f of object o".left)
      } yield h |> _ch_refenv.modify(_.updated(o, rs.updated(f, os2)))
    else s"$f neither a child nor reference".left
  }

  private def evalBasicExpr(e: BasicExpr, stack: CStack): String \/ Instances = e match {
    case Symbol(id) => "Unexpected symbol in concrete expression".left
    case Var(name) => stack.get(name).cata(
      res =>
        if (res.size == 1) res.head.right
        else s"$name contains a set of instances".left,
      s"Unknown variable $name".left
    )
  }

  private def evalExpr(e: SetExpr, stack: CStack): String \/ Set[Instances] = e match {
    case SetLit(es @ _*) => es.toSet.traverseU(e => evalBasicExpr(e, stack))
    case Union(e1, e2) => for {
      os1 <- evalExpr(e1, stack)
      os2 <- evalExpr(e2, stack)
    } yield (os1 union os2)
    case Diff(e1, e2) => for {
      os1 <- evalExpr(e1, stack)
      os2 <- evalExpr(e2, stack)
    } yield (os1 diff os2)
    case ISect(e1, e2) => for {
      os1 <- evalExpr(e1, stack)
      os2 <- evalExpr(e2, stack)
    } yield (os1 intersect os2)
    case SetVar(name) => stack.get(name).cata(_.right, s"Unknown variable $name".left)
    case SetSymbol(c, id) => "Unexpected symbol in concrete expression".left
  }

  private def evalBoolExpr(b: BoolExpr, stack: CStack, heap: CHeap): String \/ Boolean = b match {
    case Eq(e1, e2) => for {
      os1 <- evalExpr(e1, stack)
      os2 <- evalExpr(e2, stack)
    } yield e1 == e2
    case ClassMem(e, c) => for {
      os <- evalExpr(e, stack)
      types <- os.traverseU(o => heap.typeenv.get(o).cata(_.right, s"Unknown instance $o".left))
      sts <- defs.subtypesOrSelf.get(c).cata(_.right, s"Unknown class $c".left)
    } yield types.forall(sts.contains)
    case SetMem(be1, e2) => for {
      o <- evalBasicExpr(be1, stack)
      os <- evalExpr(e2, stack)
    } yield os.contains(o)
    case SetSubEq(e1, e2) => for {
      os1 <- evalExpr(e1, stack)
      os2 <- evalExpr(e2, stack)
    } yield os1 subsetOf os2
    case True => true.right
    case And(b1, b2) => for {
      bb1 <- evalBoolExpr(b1, stack, heap)
      bb2 <- evalBoolExpr(b2, stack, heap)
    } yield bb1 && bb2
    case Not(b) => for {
      bb <- evalBoolExpr(b, stack, heap)
    } yield !bb
  }

  // TODO Convert use of set to use of Process (making it lazy)
  private def evalMatchExpr(m: MatchExpr, stack: CStack, heap: CHeap): String \/ Set[Instances] = {
    def match_it(os_types: Set[(Instances, Class)], c: Class): Set[Instances] = {
      os_types.filter(oc => defs.subtypesOrSelf(c).contains(oc._2)).map(_._1)
    }
    def descendants_or_selves(os: Set[Instances]): String \/ Set[Instances] = {
      for {
        cos <- os.traverseU(o =>
          heap.childenv.get(o).cata(
            _.values.toSet.flatten.right,
            s"Unknown instance $o".left
          )).map(_.flatten)
        dos <- descendants_or_selves(cos)
      } yield os ++ dos
    }
    m match {
      case MSet(e) => evalExpr(e, stack)
      case Match(e, c) => for {
        defc <- defs.get(c).cata(_.right, s"Unknown class $c".left)
        os <- evalExpr(e, stack)
        os_types <- os.traverseU(o => heap.typeenv.get(o).cata(t => (o, t).right, s"Unknown instance $o".left))
      } yield match_it(os_types, c)
      case MatchStar(e, c) => for {
        defc <- defs.get(c).cata(_.right, s"Unknown class $c".left)
        os <- evalExpr(e, stack)
        dos <- descendants_or_selves(os)
        dos_types <- dos.traverseU(o => heap.typeenv.get(o).cata(t => (o, t).right, s"Unknown instance $o".left))
      } yield match_it(dos_types, c)
    }
  }

  private val symCounter = Counter(0)

  private def freshInstance: Instances = symCounter++
}
