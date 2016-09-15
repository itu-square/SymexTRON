## Description of TRON Abstract Syntax

### Type Definitions

The `Class` type is just a tagged string.
```scala
case class Class(name: String)
```

The `Cardinality` type represents possible cardinalities of class field definitions, specifically
use `Req` for exactly 1, `ManyReq` for 1 or more, `Opt` for at most 1, and `ManyOpt` for 0 or more.
```scala
sealed trait Cardinality { def isOptional: Boolean }
case object Req extends Cardinality { def isOptional = false }
case object ManyReq extends Cardinality { def isOptional = false}
case object Opt extends Cardinality { def isOptional = true }
case object ManyOpt extends Cardinality { def isOptional = true }
```

The `FieldType` is used mostly in conjunction with model transformation language examples, where `Tracking` means that the field is there to be
used to intermediately track mappings between types from input meta-model to output meta-model, and `Bidirectional` specifies that the field has corresponding
opposite field which is specified by specifying the field name (note that `Fields` is an alias for string). `Ordinary` is the default value to provide when the field does not have any of these extended behaviours.
```scala
sealed trait FieldType
case object Ordinary extends FieldType
case object Tracking extends FieldType
case class Bidirectional(oppositeOf: Fields) extends FieldType
```

The `FieldDefinition` represents the required information to define a field (except its name), which is its target class, its cardinality
and its field type.

```scala
case class FieldDefinition(`class`: Class, card: Cardinality, fieldtype: FieldType)
```

A `ClassDefinition` is used to define a class with a particular `name`, two map from field names to field definitions (one for containment fields, and the other for ordinary fields),
an optional super-class, a parameter `isStandalone` to specify whether the instances of this class are uncontained in general (like Strings or Ints) and
a parameter `isAbstract` to specify whether it is possible to construct concrete instances of the class.
```scala
// We only support single inheritance
case class ClassDefinition(name: String, children: Map[Fields, FieldDefinition],
                           refs: Map[Fields, FieldDefinition], superclass: Option[Class] = None, isStandalone: Boolean = false, isAbstract: Boolean = false)
```

### Program Syntax

The program AST uses light-weight GADTs inorder to increase sharing between the program and symbolic versions of the program syntax.
We therefore define a type-level enumeration:

```scala
sealed trait ASTType
case object IsSymbolic extends ASTType
case object IsProgram extends ASTType
```

Our set expression syntax represent possible set expressions union `Union`, difference `Diff`, intersection `ISect` and variables `Var`.
In addition, symbolic expression may contain set symbols `SetSymbol` and non-empty set literals with explicit cardinality `SetLit`.
```scala
sealed trait BasicExpr[T <: ASTType]
case class Symbol(id: Symbols) extends BasicExpr[IsSymbolic.type]

sealed trait SetExpr[T <: ASTType]
case class SetLit[T <: ASTType](es: Seq[BasicExpr[T]]) extends SetExpr[T]
case class Union[T <: ASTType](e1 : SetExpr[T], e2 : SetExpr[T]) extends SetExpr[T]
case class Diff[T <: ASTType](e1 : SetExpr[T], e2 : SetExpr[T]) extends SetExpr[T]
case class ISect[T <: ASTType](e1 : SetExpr[T], e2 : SetExpr[T]) extends SetExpr[T]
case class Var(name: Vars) extends SetExpr[IsProgram.type]
case class SetSymbol(id: Symbols) extends SetExpr[IsSymbolic.type]
```

We also have boolean expressions over the set expressions such as equality `Eq` and subset `SetSubEq`, and ordinary Boolean connectives
like `True`, `And` and `Not`.
```scala
sealed trait BoolExpr[T <: ASTType]
case class Eq[T <: ASTType](e1: SetExpr[T], e2: SetExpr[T]) extends BoolExpr[T]
case class SetSubEq[T <: ASTType](e1: SetExpr[T], e2: SetExpr[T]) extends BoolExpr[T]
case class And[T <: ASTType](b1: BoolExpr[T], b2: BoolExpr[T]) extends BoolExpr[T]
case class True[T <: ASTType]() extends BoolExpr[T]
case class Not[T <: ASTType](b: BoolExpr[T]) extends BoolExpr[T]
```

Our match expressions abstract syntax is only used for programs, and has three constructors:
`MSet` which lifts an ordinary set expression to a `MatchExpr` (i.e. to use in foreach-loops), and
`Match` and `MatchStar` which represent shallow and deep matching respectively, and accept a set expression and target class to match on.
```scala
sealed trait MatchExpr
case class MSet(e : SetExpr[IsProgram.type]) extends MatchExpr
case class Match(e : SetExpr[IsProgram.type], c : Class) extends MatchExpr
case class MatchStar(e : SetExpr[IsProgram.type], c : Class) extends MatchExpr
```

Finally, our program syntax consists of the various kinds of TRON statements: sequencing `StmtSeq`, variable assignment `AssignVar`,
field access `LoadField` and update `AssignField`, instance creation `New`, if-statements `If`, foreach-statements `For` and
fix-statements `Fix`. All the constructors accept only program set expressions, and takes a `metaInf` argument which allows encoding
of various kinds of meta-information during processing.
```scala
sealed trait Statement
case class StmtSeq(metaInf: Statement.MetaInf, ss : Seq[Statement])
  extends Statement
case class AssignVar(metaInf: Statement.MetaInf, x : Vars, e : SetExpr[IsProgram.type])
  extends Statement
case class LoadField(metaInf: Statement.MetaInf, x : Vars, e : SetExpr[IsProgram.type], f : Fields)
  extends Statement
case class New(metaInf: Statement.MetaInf, x : Vars, c : Class)
  extends Statement
case class AssignField(metaInf: Statement.MetaInf, e1 : SetExpr[IsProgram.type], f : Fields, e2 : SetExpr[IsProgram.type])
  extends Statement
case class If(metaInf: Statement.MetaInf, cond: BoolExpr[IsProgram.type], ts : Statement, fs : Statement)
  extends Statement
case class For(metaInf: Statement.MetaInf, x: Vars, m: MatchExpr, sb: Statement)
  extends Statement
case class Fix(metaInf: Statement.MetaInf, e : SetExpr[IsProgram.type], sb: Statement)
  extends Statement
```

To make it easier to construct statements without having to consider meta-information, we have also suitable smart constructors available:
```scala
def stmtSeq(ss : Statement*) : Statement = StmtSeq(NoMI, ss)
def assignVar(x : Vars, e : SetExpr[IsProgram.type]) : Statement = AssignVar(NoMI, x, e)
def loadField(x : Vars, e : SetExpr[IsProgram.type], f : Fields) : Statement = LoadField(NoMI, x, e, f)
def `new`(x : Vars, c : Class) : Statement = New(NoMI, x, c)
def assignField(e1 : SetExpr[IsProgram.type], f : Fields, e2 : SetExpr[IsProgram.type]) : Statement = AssignField(NoMI, e1, f, e2)
def `if`(cond: BoolExpr[IsProgram.type], ts : Statement, fs : Statement) : Statement = If(NoMI, cond, ts, fs)
def `for`(x : Vars, m : MatchExpr, s : Statement) : Statement = For(NoMI, x, m, s)
def fix(e : SetExpr[IsProgram.type], s : Statement) : Statement = Fix(NoMI, e, s)
```
