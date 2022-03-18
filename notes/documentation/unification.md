Unification
===

Unification, in general, is the process of solving equation of symbolic trees.
This page focuses on one-sided unification (also known as matching).
Formally, given a value and a pattern, it consists in finding an assignment
for the variables in the pattern such that when instantiated the pattern becomes
equivalent to the value.

In LISA we are interested to do unification on terms and formulas because it enables
us to automatically instantiate schemas and binders in situations where the expected
assignment can be inferred.

Unification in LISA is made more interesting thanks to the equivalence checker,
which redefines the notion of "equivalence" and poses the additional challenge
to try to benefit from it.

### One-sided unification with simple unknowns

Here the pattern is only allowed to contain nullary schemas.
This problem is essentially pattern matching and relatively straightforward to solve.

It is the algorithm that is currently implemented for the front.

It features additional functionalities such as:
* Bound variable renaming: names of variables do not matter
* Equivalence checking at the level of the unknowns

This procedure is thought to be complete and exact (modulo equivalence), meaning that any existing solution
should be equivalent to a solution that was returned (and it can only return at most one of them).

Values are normally allowed to have schemas in them as these should be treated
no differently than regular values.

Examples:

|          Pattern           |            Value            | Possible result  |
|:--------------------------:|:---------------------------:|:----------------:|
|         `a /\ ?b`          |          `a /\ c`           |   `{?b -> c}`    |
|         `?a => ?a`         |   `(a \/ b) => (b \/ a)`    | `{?a -> a \/ b}` |
|         `?a \/ ?b`         |       `a => (a \/ b)`       |   `impossible`   |
| `forall x, y. f(x, y, ?z)` | `forall w, z1. f(w, z1, x)` |   `{?z -> x}`    |
|       `forall x. ?a`       |      `forall x. x = x`      |   `impossible`   |

As the last example demonstrates, extra care should be taken with free/bound variables.

### One-sided unification with parametrized unknowns

> _This section is speculative._

Questions:
* Are schemas allowed to be nested?
* How to handle schemas in values? (which should be treated as values)
* Are connector schemas required/allowed?

|           Pattern            |              Value              |            Possible result             |
|:----------------------------:|:-------------------------------:|:--------------------------------------:|
|      `forall x. ?f(x)`       |        `forall x. x = y`        |         `{?f -> \x. (x = y)}`          |
|  `forall x. ?f(x, y) /\ ?a`  | `forall x1. (x1 = {y, z}) /\ b` | `{?a -> b, ?f -> \x, y. (x = {y, z})}` |
|       `?f(?g(x)) = {}`       |         `{x, {}} = {}`          |                 `???`                  |
