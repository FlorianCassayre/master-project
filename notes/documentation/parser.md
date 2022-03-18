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

The "grammar" of LISA is not set in stone and may change in the future.

The printer does not yet support the `\x1, ..., xn. ...` syntax.

The string representation of proofs is ambiguous: by omitting the proof steps parameters, it is not
always possible to reconstruct the exact same proof step, or to reconstruct it at all.

These issues shall be addressed later when the parser is expected to play a more
important role.

### Specification

#### Grammar

We present the grammar in terms of tokens. For instance `"<=>"` does not correspond to the
string `<=>` but rather the token representing this symbol. The ASCII lexer will parse
the string `"<=>"` as this token, while the unicode one will parse `↔`.

```
id  ::= [a-zA-Z_][a-zA-Z0-9_]*
sid ::= \?[a-zA-Z_][a-zA-Z0-9_]*
ol2 ::= "<=>" | "=>" | "\/" | "/\" | "in" | "sub" | "~" | "="
bl  ::= "forall" | "exists" | "existsone"

t   ::= t ol2 t
      | "!" t
      | bl id "." t
      | "{}" | "{" t "}" | "{" t "," t "}"
      | (id | sid) ("(" t ("," t)* ")")?
      | "(" t ")"

tt  ::= "\" id ("," id)* "." t

tts ::= (tt (";" tt)*)?
s   ::= tts "|-" tts
```

#### Associativity & precedence

All infix binary operators are defined to associate to the right.
The precedence of these operators is independent of the type of their arguments.
The operators below are sorted by their precedence (from lowest to highest;
same line means equal precedence):

```
<=>
=>
\/
/\
in, sub, ~, =
!
()
```

Binders always capture the largest possible formula.

#### Term and formula resolution

The rules for resolution are given below. There are two types, terms (`T`) and formulas (`F`).
Knowing the type of the top-level term can allow us to resolve the full tree into terms
and formulas. The last case (nullary function / variable) is resolved by looking in the
environment: if there is a variable wih that name in the context, then this symbol should be
a variable.

```
C, x1, ..., xn |- a: F
-----------------------
C |- \x1, ..., xn. a: F 

 C, x |- a: F
-------------- [Binder(B, x, a)]
C |- B x. a: F (B is one of: forall, exists, existsone)

C |- a: F
---------- [Connector(Neg, a)]
C |- !a: F

C |- a: F    C |- b: F
---------------------- [Connector(op, (a, b))]
    C |- a op b: F     (op is one of: /\, \/, =>, <=>)

C |- x1: T  ...  C |- xn: T
--------------------------- [Function((?)f, (x1, ..., xn))]
 C |- (?)f(x1, ..., xn): T

C |- a: T    C |- b: T
---------------------- [Predicate(op, (a, b))]
    C |- a op b: F     (op is one of: in, sub, ~, =)

C |- x1: T  ...  C |- xn: T
--------------------------- [Predicate((?)f, (x1, ..., xn))]
 C |- (?)f(x1, ..., xn): F

------------ [Predicate((?)c, ())]
C |- (?)c: F

---------- [Function(?c, ())]
C |- ?c: T

--------- [Function(c, ())]
C |- c: T (if c is not in C)

------------ [Variable(c)]
C, c |- c: T
```

Additional predefined constant operators have similar rules to the ones presented above.

In the future we may allow type ascriptions, as displayed in these rules.

#### Proofs

A proof is internally represented as nested indexed sequences of steps.
Each line starts with an integer, representing the step's index. These indices
can be indented but are always right aligned.

For instance, the following indices are properly aligned:
```
  -2
  -1
   0
   1
```

While these indices aren't properly aligned (they appear on two distinct levels):
```
  -2
  -1
  0
  1
```

Then follows the rule name, the indices of the premises (if any) and the bottom sequent.
Only the indentation of the step index matters, and different branches do not need to be indented
the same way.
