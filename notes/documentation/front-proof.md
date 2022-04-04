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

In the front, proofs are represented in **backward mode**.
The user must initially state the conclusion (a sequent) and show that all the branches
of the proof are closed.

Formally:
* **Proof state**: a collection of independent proof goals
* **Proof goal**: a sequent that needs to be proven
* **Tactic**: a function that takes a proof goal and returns a sequence of new proof goals
* **[name tbd]** (state-level tactic): a function that takes a proof state a returns a new proof state
* **[name tbd]** (proof-level tactic): a function that takes a proof tree and returns a new proof tree

The objective is thus to apply the correct rules to eventually eliminate all proof goals.

If a proof state initially contains a sequent, then that sequent is said to be **proven**
if a certain sequence of tactics reduces the proof state to an **empty** state.

A key property of the front is its ability to **reconstruct** a kernel proof
from any front proof. This is crucial because to guarantee the correctness of a proof that
was written in the front, we only need to trust the kernel. That way the implementation of
the kernel remains lightweight, while the front can be as sophisticated as desired.

To achieve that, every tactic must return (in addition to the new proof state) a function
that describes the reconstruction in terms of kernel steps. In proof mode, the front keeps
track of the evolution of the proof state. Once the proof is finished, it works its way
backwards by joining the different kernel steps fragments together.

Of course the front may contain bugs and allow the creation of false proofs,
or fail to perform the reconstruction altogether. This is clearly not desirable, however we
can only provide guarantees regarding the proofs that can be reconstructed and be verified 
by the kernel.
In practice, we can set some safeguards such as limiting the ability to create tactics
that can return arbitrary (and potentially incorrect) kernel proofs steps. We can also
perform local checks to let the failure happen as early as possible.

#### Rules

**Rules** are a special class of functions that can produce tactics.

They are described by three pieces of information:
* **Hypotheses**: any number of partial sequents
* **Conclusion**: one partial sequent
* **Reconstruction**: a way to reconstruct an application of this rule into kernel proof steps

The rule below is an example of a rule (the reconstruction is shown later):
```
... |- ?a, ...    ... |- ?b, ...
================================
      ... |- ?a /\ ?b, ...
```

The intended (forward) semantic is the following:
* Provided two sequents having a formula on the right
* Infer a new sequent containing the conjunction of the two formulas on the right

In backward mode, the behavior is the opposite: the hypotheses are derived from
the conclusion.

The schemas (symbols starting with `?`) can match any tree.
The wildcards `...` are expected to match any number of formulas, and not modify them.
Moreover, the wildcards at the bottom should be the union of the ones are the top.

The reason rules do not directly inherit from tactics is because they need additional
parameters to be applied. For instance, we need to know which formulas correspond to
what pattern, and the assignment of the schemas. Sometimes, these parameters can be
inferred implicitly.

The reconstruction scheme of the previous example is the following:
```
IndexedSeq(
  RightAnd(bot, Seq(-1, -2), Seq(ctx(a), ctx(b)))
)
```
Where `a`, `b` are the schematic labels and `ctx` the resolution function.
The indices `-1` and `-2` respectively match the first and second subgoals created by this rule.

It's possible to return more than one step, although in practice we should
avoid inlining long proofs but rather factor parts of them into intermediate
theorems that can be later instantiated.

The next logical step was to integrate schemas with arbitrary arity.
This allows us to write the remaining rules of sequent calculus, such as right substitution:
```
... |- ?f(?a), ...    ... |- ?a <-> ?b, ...
===========================================
            ... |- ?f(?b), ...
```

> _Currently rules do not automatically infer schemas of higher order; the user must
> specify them explicitly._

One of the benefit of describing rules using this declarative syntax is that it's concise,
and versatile (no need to implement specialized code, everything is handled by the same procedure).

That said, the main advantage of rules is that they can be applied in both directions.
This is explained later.

#### Environment

The previous parts mostly focused on what happens in proof mode.

In order to reduce the length of proofs and repetition of proof steps, we introduce
the concept of **justifications**. This concept is very similar to what is implemented in
the LISA kernel, which is itself borrowed from LCF. Namely, a justification is a statement
(= sequent) that can be used as a justification step in a proof. They come in three flavours:
* **Axioms**: these are statements that are assumed as part of a _theory_.
* **Theorems**: any valid proof can be converted into a theorem
* **Definitions**: needed to define and use new symbols

Axioms are required to define theories. Theorems and definitions play an important role
in making the system more usable and reducing the length of proofs. For example, once a
theorem is used, we don't need to reconstruct the underlying proof more than once, since
all the usages will rely on its conclusion alone.

Proofs can therefore depend on other justifications. For that, a special tactic
`TacticApplyJustification` is provided and is going to eliminate a goal assuming it corresponds
to an existing justification in the theory.

The front provides the guarantee that any instance of `Jutified` has a valid counterpart
instance in the kernel, and thus that the proof is valid.

#### Tactics

Tactics come in different flavours.

At the proof goal level:
* Regular tactics: this is the kind of tactics that is created by rules. Solvers can
  be implemented through these as well.
* Theorem application: as explained previously, this tactic eliminates the goal
  if it is considered to be a valid justification.

At the proof state level:
* Focus proof goal: to prove a different goal than the one currently select.

At the proof tree level:
* Cancel the last step: in case the user made mistake, this command restores the proof state
  to its original state prior to the last step.


Moreover, the following should also be possible (but are not currently implemented):
* Repeated tactic: we should have a tactic that repeats another tactic until it fails.
  Similarly, we should also provide the ability to apply a tactic on all formulas of a sequent (this might be tricky).
* Composed tactic: tactics should be composable with each other (chained). This may seem trivial
  at first, but there are various problems that need to be overcome in order to make the feature
  practical.

#### Forward proofs

Until now, we have only described the backward mode.
However, it is also possible given a justification to produce a new theorem. This is what we call
**forward mode**.

Fundamentally, both modes are equally powerful and thus equivalent. In practice, it is sometimes
easier to use a combination of both.

For example, if we want to show a particular case of the symmetry of equality, then it
would be much more natural to first prove the general case and then instantiate it
with respect to our needs:
```
?s = ?t |- ?t = ?s     ===>     {} = {{}} |- {{}} = {}
```

This example showed schema instantiation.

In general, any rule can be used in forward mode, for free. On the other hand, tactics
are implemented for backward mode only. If the user desires to have additional forward
mode procedures, they should define these themselves.
