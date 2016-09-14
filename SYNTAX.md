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
opposite field which is specified by specifying the field name. `Ordinary` is the default value to provide when the field does not have any of these extended behaviours.
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
