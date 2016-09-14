# SymexTRON
![GPLv3 licensed](README/GPLv3-badge.png)

A tool for symbolically executing TRON programs and generate white-box tests.

### Prerequisites

* Scala 2.11 (tested with 2.11.8)
* SBT   0.13 (tested with 0.13.12)
* Internet access for SBT to download dependencies

To run the native Plingeling solver, you must have the `lib/solvers/‹platform›` folder on your `java.library.path` (where `‹platform›` should be replaced by either `darwin` (for OS X) or `linux`).
This can be achieved by changing the setting in the repository included `.sbtopts` file.
In case no native solver is available, it will fallback to the Java SAT4J solver which is compatible with more platforms but is slower.

### To build:

First go to the source directory by using `cd $HOME/Documents/SymexTRON` and then call `sbt compile`.

### To run tests:

Call `sbt test` in the SymexTRON directory.

### To run the SLE paper evaluation:

Call `sbt run` in the SymexTRON directory.

The main evaluation source file is `src/main/scala/examples/evaluation/Evaluation.scala`, and it uses some of the example files
from the containing `examples` folder.

The evaluation subjects from the paper and accompanying technical report can be found as follows:

| Program              | File                            | Object                              |
| ---------------------|---------------------------------|-------------------------------------|
| RenameField          | Refactoring.scala               | RenameFieldRefactoring              |
| RenameMethod         | Refactoring.scala               | RenameMethodRefactoring             |
| ExtractSuper         | Refactoring.scala               | ExtractSuperclassRefactoring        |
| ReplaceDelegation    | Refactoring.scala               | ReplaceDelegationWithInheritance    |
| Fam2Pers             | ATLModelZooTransformation.scala | FamiliesToPersonsTransformation     |
| Path2Petri           | ATLModelZooTransformation.scala | PathExp2PetriNetTransformation      |
| Class2Rel            | ATLModelZooTransformation.scala | ClassToRelationalTransformation     |
| Toy1                 | IntListExample.scala            | IntListContainsElementExample       |
| Toy2                 | IntListExample.scala            | IntListHeadTailEqExample            |
| Toy3                 | Class2TableExample.scala        | Class2TableSimpleExample            |
| Toy4                 | Class2TableExample.scala        | Class2TableDeepMatchingExample      |
| Toy5                 | BlogPostFeedExample.scala       | BlogPostFeedTimestampsExample       |
| Toy6                 | BlogPostFeedExample.scala       | BlogPostFeedCapitaliseTitlesExample |
| Toy7                 | ContactBookExample.scala        | ContactBookExample                  |

### To make an example program:

Make a new file with your example name e.g. `FooExample.scala` which contains an object `FooExample` that inherits from the `examples.Example` trait.
Then override the `classDefs` (containing the metamodel/type-definitions), `pres` (containing the initial memory) and `prog` (containing the TRON program) values to contain your desired program. Remember to add the following imports:

```
import semantics.domains._
import syntax.ast.Statement._
import syntax.ast._
```

For a simple example, see the `IdIterExample` in the `examples` package.

You can run an example by using `sbt 'run-main ‹example name›'`, e.g. `sbt 'run-main examples.IdIterExample'` for running the tool on the `IdIterExample`.
