Documentation: Front DSL
===

The front defines its own datastructures, eliminating the dependence of the end user
to the kernel.
There is a one-to-one translation between terms, formulas and sequents in the front and the kernel.
The representation is the same, the only difference is the interface.

Function and predicate applications are guaranteed through the Scala compiler to have
the correct number of parameters. The trees _will_ also redefine `toString`,
which is a requested feature. Moreover, the DSL is also more stable in the usage because
it limits the number of implicit conversions and extensions needed to implement the desired functionality.

Conversion functions allow translating front types and values into kernel ones.

The former kernel imports:
```Scala
import lisa.kernel.fol.FOL.*
import lisa.KernelHelpers.*
```
Have been merged in a single import:
```Scala
import masterthesis.front.fol.FOL.*
```
And additionally, all the logic related to proofs can be imported with:
```Scala
import masterthesis.front.proof.Proof.*
```
