Documentation: Usage as a library
===

For the installation, please refer to the instructions in the **[README](../../README.md)**.

Then, to get started with the front you only need to add a single import:

```Scala
import me.cassayre.florian.masterproject.front.{*, given}
```

Note that if you use the REPL (`sbt console`) this package will have already been
imported for you.

Here is a self-contained example that demonstrates some capabilities of the front:

```Scala
import me.cassayre.florian.masterproject.front.{*, given}

val (a, b, c) = (SchematicPredicateLabel[0]("a"), SchematicPredicateLabel[0]("b"), SchematicPredicateLabel[0]("c"))
val (s, t, u) = (SchematicFunctionLabel[0]("s"), SchematicFunctionLabel[0]("t"), SchematicFunctionLabel[0]("u"))
val (x, y, z) = (VariableLabel("x"), VariableLabel("y"), VariableLabel("z"))

given ProofEnvironment = newEmptyEnvironment()

val theorem1 = {
  val proofMode = ProofMode((a \/ b) |- (b \/ a))
  import proofMode.*

  apply(introLOr)
  apply(solveProp)
  apply(solveProp)

  asTheorem()
}

theorem1(b, b \/ c).display()
```

For further details about the exact syntax and possibilities offered, please refer to **[Front DSL](front-dsl.md)**
and **[Front Proof](front-proof.md)**.
