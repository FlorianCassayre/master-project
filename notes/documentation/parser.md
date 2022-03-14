Documentation: Parser
===

The package `parser` contains all the logic responsible for parsing
the LISA syntax, as produced by the printer (`lisa.kernel.Printer`).

* `SCReader.readFormulaAscii` -- reads a formula in ASCII. Examples:
  ```
  c
  (a /\ b) => (c <=> d)
  f(a, b)
  exists x. !(x in {})
  forall x, y. {x, y} = {y, x}
  ```
* `SCReader.readSequentAscii` -- reads a sequent in ASCII. Examples:
  ```
  |-
  |- a
  a; b |- c; d
  exists x. g(x); a /\ b |- a; b
  ```
* `SCReader.readProof` -- reads a proof in its standard format. Example:
  ```
  -1        Import 0    ⊢ ∀x, y, z. (z ∈ {x, y}) ↔ (x = z) ∨ (y = z)
   0        Rewrite -1  ⊢ ∀x, y, z. (z ∈ {x, y}) ↔ (x = z) ∨ (y = z)
   1        Subproof -1 ⊢ ∀y, z. (z ∈ {x, y}) ↔ (x = z) ∨ (y = z)
     -1     Import 0    ⊢ ∀x, y, z. (z ∈ {x, y}) ↔ (x = z) ∨ (y = z)
      0     Subproof    ∀x, y, z. (z ∈ {x, y}) ↔ (x = z) ∨ (y = z) ⊢ ∀y, z. (z ∈ {x, y}) ↔ (x = z) ∨ (y = z)
        0   Subproof    ∀x, y, z. (z ∈ {x, y}) ↔ (x = z) ∨ (y = z) ⊢ ∀y, z. (z ∈ {x, y}) ↔ (x = z) ∨ (y = z)
          0 Hypo.       ∀y, z. (z ∈ {x, y}) ↔ (x = z) ∨ (y = z) ⊢ ∀y, z. (z ∈ {x, y}) ↔ (x = z) ∨ (y = z)
          1 Left ∀ 0    ∀x, y, z. (z ∈ {x, y}) ↔ (x = z) ∨ (y = z) ⊢ ∀y, z. (z ∈ {x, y}) ↔ (x = z) ∨ (y = z)
      1     Cut -1, 0   ⊢ ∀y, z. (z ∈ {x, y}) ↔ (x = z) ∨ (y = z)
   2        Hypo.       ∀z. (z ∈ {x, y}) ↔ (x = z) ∨ (y = z) ⊢ ∀z. (z ∈ {x, y}) ↔ (x = z) ∨ (y = z)
   3        Left ∀ 2    ∀y, z. (z ∈ {x, y}) ↔ (x = z) ∨ (y = z) ⊢ ∀z. (z ∈ {x, y}) ↔ (x = z) ∨ (y = z)
   4        Cut 1, 3    ⊢ ∀z. (z ∈ {x, y}) ↔ (x = z) ∨ (y = z)
   5        Hypo.       (z ∈ {x, y}) ↔ (x = z) ∨ (y = z) ⊢ (z ∈ {x, y}) ↔ (x = z) ∨ (y = z)
   6        Left ∀ 5    ∀z. (z ∈ {x, y}) ↔ (x = z) ∨ (y = z) ⊢ (z ∈ {x, y}) ↔ (x = z) ∨ (y = z)
   7        Cut 4, 6    ⊢ (z ∈ {x, y}) ↔ (x = z) ∨ (y = z)
  ```

### Pipeline

The parsing works in three steps:
* `SCLexer` transform a stream of characters into a stream of lexical tokens (`SCToken`)
* `SCParser` parses the tokens into a tree (`SCParsed`)
* `SCResolver` resolves a parsed tree into a kernel structure (`SCResolver`)

`SCReader` is the public interface and is responsible for calling the steps in sequence.

### Caveats

The "grammar" of LISA is not set in stone. It contains in fact an ambiguity.
The ambiguity comes from terms: there is no syntactical difference
between variables and non-standard nullary constants. Thus, we currently assume
all such terms to be variables.

The proofs are also ambiguous: by omitting the proof steps parameters, it is not
always possible to reconstruct the exact same proof step, or to reconstruct it at all.

These issues shall be addressed later when the parser is going to play a more
important role.
