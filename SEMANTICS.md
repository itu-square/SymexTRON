## Description of semantics

### Symbolic semory description
The symbolic stack representation is simple, keeping track of two things: a mapping between variables and symbolic expressions, and a set of variables which may act as the root of an instance structure (used primarily for model transformations).
To construct a stack use the following function:

```scala
SStack.initial(roots: Set[Vars], sstackstate: SStackState)
```

The symbolic heap representation consists of 5 components: a map keeping track of set symbol information `ssvltion`, a map keeping track of symbolic reference information `svltion`, a map tracking how symbolic instances were created `locOwnership`, a map that gathers spatial constraints over symbolic instances, and a set of pure boolean constraints `pure`. When constructing the initial heap, we recommend using negative integer identifiers for symbols in order to avoid clashing with the symbol generator that is used by the executor (since its starts at 0).

You can construct a symbolic heap by using:
```scala
SHeap.initial(ssvltion : SetSymbolValuation, svltion : SymbolValuation, locOwnership: LocOwnership, spatial : Spatial, pure: Prop)
```

`SetSymbolValuation` is an alias for `Map[SetSymbol, SSymbolDesc]`, where `SSymbolDesc` is defined as follows:
```scala
case class SSymbolDesc(cl : Class, notinstof: Set[Class], crd : Cardinality)
```
It basically tracks the type-bounds and cardinality of the set symbol during execution.

`SymbolValuation` is an alias for `Map[Symbol, SymbolDesc]`, where `SymbolDesc` is defined as:
```scala
sealed trait SymbolDesc
case class Loced(l : Loc) extends SymbolDesc
case class UnknownLoc(cl : Class, notinstof: Set[Class]) extends SymbolDesc
```
Basically, either a symbolic reference is already assigned a location and so it tracks the assigned location via `Loced`; otherwise
it's not and so it keeps track of the required type-bounds.

`LocOwnership` is an alias for `Map[Loc, Ownership]`, where `Loc` and Ownership` are defiend as:

```scala
case class Loc(id: Int)

sealed trait Ownership
case object NewlyCreated extends Ownership
case object Unfolded extends Ownership
```
A location has a unique integer identifier, and the ownership enumeration keeps track of whether the symbolic instance was created explicitly by the user (by using `new`) or it was created internally by the executor when unfolding symbols.

The `Spatial` component is a map between symbolic instances and spatial constraint descriptions `Map[Loc, SpatialDesc]`.
A spatial constraint description is defined as follows:
```scala
case class SpatialDesc(cl : Class, notinstof : Set[Class], desctype : DescType, 
                       children : Map[Fields, SetExpr[IsSymbolic.type]], 
                       refs : Map[Fields, SetExpr[IsSymbolic.type]], 
                       descendantpools: DescendantPools)
```
It keeps track of the type-bounds, a description type, contraint maps of contained and referenced fields `children` and `refs`,
and a set of deep containment constraints `descendantpools`.

The description type `DescType` has following shape:
```scala
sealed trait DescType
case object ExactDesc extends DescType
case object AbstractDesc extends DescType
case class PartialDesc(hasExact: Boolean, possible: Set[Class]) extends DescType
```

It is either an exact description (so all fields are present), a partial description (so it only describes the subset of fields, that are bounded by the type-bounds upper class), or an abstract description (with no fields defined so far).

Finally, `Prop` is just an alias of `BoolExpr` which represents pure constraints.

A symbolic memory, consists of a symbolic stack and heap:

```scala
case class SMem(stack: SStack, heap: SHeap)
```
