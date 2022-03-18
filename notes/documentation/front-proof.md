Documentation: Front Proof
===

The "front" (package `front`) is a different layer that is being developed in this project.
It depends on the kernel and aims to be a more convenient interface for the end user (see [Front DSL](front-dsl.md)).
The concepts of terms, formulas and sequents are exactly the same as in the kernel.
The difference comes from the representation of proofs.

### Proofs in the kernel

In the kernel, a proof is represented as a DAG (directed acyclic graph).
The following example illustrates the structure of such a proof (this syntax is fictitious):
```
0   a |- a
1   a |- (a \/ a) by 0
2   (a \/ a) |- a by 0
3   |- (a ==> (a \/ a)) by 1
4   |- ((a \/ a) ==> a) by 2
5   |- (a <=> (a \/ a)) by 3, 4
```
Each step depends on zero or more previous steps (premises).
The conclusion of a proof corresponds to the conclusion (sequent) of the last step,
here `|- f <=> (f \/ f)`.

### Proofs in the front

In the front, proofs are represented in the opposite direction.
The user must initially state the conclusion, and then provide a sequence
of rules and tactics that reduces this sequent to something that does not
depend on any hypotheses.

Formally we have:
* **Proof state**: a sequence of proof goals
* **Proof goal**: a sequent that needs to be proven
* **Rule** or **tactic**: a function that ingests a proof goal and returns a sequence of new proof goals

The objective is thus to apply the correct rules to eventually eliminate all proof goals.

A key property of the front is its ability to **reconstruct** a kernel proof
from any front proof. This is crucial because to guarantee the correctness of a proof that
was written in the front, we only need to trust the kernel.

To achieve that, we work our way backwards; in addition to returning the new proofs goals,
each tactic returns a callback function that can be used to reconstruct the kernel proof
steps, once the premises are known.

Of course the front may contain bugs and allow the creation of false proofs,
or fail to perform the reconstruction altogether. This is clearly not desirable, however we
can only provide guarantees regarding the proofs that can be reconstructed and be verified by the kernel.

#### Rules

**Rules** are a subset of **tactics**.

They are tactics whose behavior can be described in a deterministic way.
The rule below is an example of a rule:

```
... |- ?a, ...    ... |- ?b, ...
================================
      ... |- ?a /\ ?b, ...
```

Provided the right parameters (some of which can even be inferred automatically),
it is possible to know in advance what the result should be. Here the formula containing
the conjunction will be destroyed and two new goals will be created with new formulas.
The `...` states that the other formulas should not be modified.
`?a` and `?b` are "holes" in the formulas (or more precisely, nullary schemas).
They enable a more expressive language to write rules.

This rule also provides the following reconstruction scheme:
```
IndexedSeq(
  RightAnd(bot, Seq(-1, -2), Seq(ctx(a), ctx(b)))
)
```
Where `a`, `b` are the schematic labels and `ctx` the resolution function.
The indices `-1` and `-2` respectively match the first and second subgoals created by this rule.

It's possible to return more than one step, although in practice we should
avoid inlining long proofs but rather factor parts of them into intermediate
theorems.

> _The front does not currently have a context to store theorems, this feature is currently being worked on._

The next logical step was to integrate schemas with arbitrary arity.
This is more difficult and currently only partially implemented.
It makes it possible to write the following rule for right substitution:
```
... |- ?f(?a), ...    ... |- ?a <-> ?b, ...
===========================================
            ... |- ?f(?b), ...
```

The main advantage of describing rules using this declarative syntax is that it's simple, and
versatile (no need to implement specialized code, everything is handled by the same procedure).

#### Tactics

> _As of now, rules are the only tactics implemented; thus what follows is purely speculative._

Tactics should come in different flavours:
* Rules as we have seen are relatively simple by design
* Tactics that can perform arbitrary transformations: this is a generalization of rules, with the difference
  that it won't be possible to know in advance whether this tactic can be applied without actually trying it
* Repeated tactic: we should have a tactic that repeats another tactic until it fails.
  Similarly, we should also provide the ability to apply a tactic on all formulas of a sequent (this might be tricky)
* Composed tactic: tactics should be composable with each other (chained). This may seem trivial
  at first, but there are various problems that need to be overcome in order to make the feature
  practical

#### Forward and backward proofs

Another advantage of describing rules with schemas is that we can use them without modifications
in both forward and backward proof styles. 
