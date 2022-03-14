Documentation: Kernel Proof Builder
===

These features correspond to older exploratory work in the kernel.
They offer an intermediary interface to the kernel, one that has a more direct
correspondence.

### `SCProofBuilder`

Abstracts the individual kernel proof steps by removing the need to
pass inferrable arguments. A `SCHighLevelProofStep` (a proof step in this interface)
can be of two kinds:
* `SCImplicitProofStep`: defined by a conclusion sequent and a sequent of premises; the interface
  will try to reconstruct a single kernel proof step from it
* `SCExplicitProofStep`: a capsule for kernel proof steps; useful in the case of steps that
  cannot be automatically inferred

The logic responsible for reconstructing the proofs steps is contained in `SCProofStepFinder`.

### `MonadicSCProofBuilder`

A DSL for the above proof builder.
As its name suggests, this module takes advantage of monads to provide a
convenient syntax for writing proofs. Here is an example showcasing all
the available features:

```Scala
val proof: SCProof = MonadicSCProofBuilder.create(for {
  (_, i0) <- MonadicSCProofBuilder.subproof(for {
    _ <- (() |- pairAxiom).justified
    _ <- withForallInstantiation(y)
    _ <- withForallInstantiation(y)
    _ <- withForallInstantiation(x)
  } yield ())
  f = y === x
  (_, i1) <- MonadicSCProofBuilder.subproof(for {
    (_, h0) <- f |- f
    (_, h1) <- f |- (f \/ f) by h0
    (_, h2) <- (f \/ f) |- f by h0
    (_, h3) <- () |- (f ==> (f \/ f)) by h1
    (_, h4) <- () |- ((f \/ f) ==> f) by h2
    _ <- () |- (f <=> (f \/ f)) by (h3, h4)
  } yield ())
  xy = y === x
  (_, i2) <- ((xy \/ xy) <=> xy) |- (xy <=> in(x, pair(y, y))) by (i0, i1)
  _ <- () |- (xy <=> in(x, pair(y, y))) by i2
  _ <- withForallGeneralization(y)
  _ <- withForallGeneralization(x)
} yield ())
```

