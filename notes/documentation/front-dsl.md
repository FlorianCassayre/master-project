Documentation: Front DSL
===

The front defines its own datastructures, eliminating the dependence of the end user
to the kernel.
There is a one-to-one translation between terms, formulas and sequents in the front and the kernel.
The representation is the same, the only difference is the interface.

Function and predicate applications are guaranteed through the Scala compiler to have
the correct number of parameters. The trees _will_ also redefine `toString`,
which was a requested feature. Moreover, the DSL is also more stable in the usage because
it limits the number of implicit conversions and extensions needed to implement the desired functionality.

Conversion functions allow translating front types and values into kernel ones.

The former kernel imports have been merged into an all-in-one import:
```Scala
import me.cassayre.florian.masterthesis.front.*
```

## API

Simplified overview of the current API.
Parentheses for default arguments can be dropped.

```
Theorem <: Justified

Rule
  apply(BParameters = empty): Tactic
  apply(FParameters = empty)(Justified*): Option[Theorem]

(introHypo, introLAnd, introRAnd, introLOr, introROr, introLImp, ...): Rule

TacticalRewrite
  apply(Sequent): Tactic
  apply(left: Map[Int, Formula], right: Map[Int, Formula]): Tactic

rewrite: Tactic
solveProp: Tactic
justification: Tactic

Justified
  rewrite(Sequent): Option[Theorem]
  rewrite(left: Map[Int, Formula], right: Map[Int, Formula]): Option[Theorem]
  apply(SchematicLabel, SchematicValue): Option[Theorem]
```

Proof mode specific syntax:

```
ProofMode:
  apply(Tactic): Boolean
  focus(Int): Boolean
  back(): Boolean
  asTheorem(): Theorem
```
