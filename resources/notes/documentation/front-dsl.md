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

## First order logic API

The FOL API is similar to LISA's. The main difference is that it is typesafe.
The number of arguments is checked at compile-time to ensure that labels
are correctly applied. This is illustrated by the following example:

```Scala
val c = ConstantPredicateLabel[0]("c")
val p = ConstantPredicateLabel[2]("p")

p(c) // error
p(c, c)
```

Sometimes it is not desirable to have this type constraint in the way, for
instance when doing pattern matching. In these cases there is an escape hatch
to get rid of this constraint:

```Scala
val c = ConstantPredicateLabel[0]("c")
val p = ConstantPredicateLabel[2]("p")

val _: PredicateFormula = PredicateFormula.unsafe(p, Seq(c, c))

val q = ConstantPredicateLabel.unsafe("q", 0)
val _: ConstantPredicateLabel[?] = q

val _: PredicateFormula = PredicateFormula.unsafe(q, Seq.empty)
```

Terms and formulas can be composed using intuitive notations:

```Scala

val c = ConstantPredicateLabel[0]("c")
val p = ConstantPredicateLabel[2]("p")

(p(c, c) /\ c) ==> c

val x = ConstantFunctionLabel[0]("x")

x === emptySet
```

The same holds for sequents:

```Scala
val c = ConstantPredicateLabel[0]("c")

() |- c
c |- (c, c, c)
```

Term, formulas and sequent all redefine `toString` according to the syntax
described [here](parser.md). Moreover, we also provide compile-time string
interpolation macros:

```Scala
val c = ConstantPredicateLabel[0]("c")
val p = ConstantPredicateLabel[2]("p")

val f: Formula = formula"$c /\ d"

formula"$p(a)" // compile-time error
formula"$p(a, b)"

sequent"|- $f; $c /\ d"
```

`unapply` is currently not implemented for these string interpolation constructs,
but it would provide similar functionality.

## Proof API

Simplified overview of the current API.
Parentheses for default arguments can be dropped.

```
Theorem <: Justified

BaseRule <: Rule
CompoundRule <: Rule

Rule
  apply(BParameters = empty): Tactic
  apply(FParameters = empty)(Justified*): Option[Theorem]
  compose(map: RCParameters): CompoundRule

(introHypo, introLAnd, introRAnd, introLOr, introROr, introLImp, ...): BaseRule

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
ProofMode
  apply(Tactic): Boolean
  repeat(Tactic): Unit
  focus(Int): Boolean
  back(): Boolean
  reset(): Unit
  asTheorem(): Theorem
```
