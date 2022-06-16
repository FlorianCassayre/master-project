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

Because it is "one-sided", schemas appearing in the value should be treated as constants.

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

The majority of rules use nothing more than nullary schemas, which can easily be unified
automatically. On top of that it is possible to consistently infer functions and predicates
that only take bound variables as arguments. The reason is that bound variables passed as
arguments can be removed (thus transforming the higher order schema into a nullary one).
This is useful for rules that introduce/eliminate quantifiers.

It appears that all the remaining problems could have multiple solutions, depending on the value
that is submitted. For instance, the pattern `?f(t)` unified with the value `t = u` has two
solutions: `{?f -> \x. x = u}` and `{?f -> \x. t = u}`. According to the definition of the
most general unifier, the selected solution in this case would be the first one.

#### Specification and sketch of a general algorithm

**Input**

* A sequence of patterns
* A sequence of values
* A partial assignment

The patterns and the values can be either terms of formulas (but should all be the same kind).
The length of the sequences should be the same.

All terms and formulas should be well-formed:
* The number of arguments in an application should match that label's arity
* A binder cannot declare a bound variable if that variable has already been declared in this scope
  (e.g. there is no restriction on sibling binders because they aren't in the same scope)

Values and partially assigned values may contain connector schemas. Because schemas in the value are
treated as atoms, those will be handled equally.

In the patterns, all declared bound variables should be distinct, and free variables should be disjoint
from bound variables. Otherwise, they would create a clash in the resulting mapping.

**Output**

An option containing a mapping between schemas & variables and assigned terms & formulas.

The mapping is defined exactly for all the schemas appearing in the patterns.

If the solution space is not infinite, and if a most general solution exists (both with
respect to the partial assignment), then it should be returned. That solution should be
a superset of the partial assignment.

If several matching assignments exist, the one appearing first according to the postorder
tree traversal is chosen (left branch, right branch, root).

**Algorithm**

The very first step of the algorithm is to rename schemas and variables (bound and free) in patterns,
such that they don't collide with names in the value.

Then we need to collect the constraints. We do that by evaluating `collect(pattern, value)({})`.
The function `collect` is defined as follows:

* Constant application

  `f` is either a constant function, predicate or connector (possibly nullary):
  ```
  collect(f(p1, ..., pn), f(v1, ..., vn))(ctx) :=
    collect(p1, v1)(ctx) U ... U collect(pn, vn)(ctx) | {}
  ```
* Schematic application

  `?f`is either a schematic function, predicate or connector (possibly nullary):
  ```
  collect(?f(p1, ..., pn), val)(ctx) :=
    {(?f, (p1, ..., pn), val, ctx)} | {}
  ```
* Binder

  ```
  collect(B x. pat, B y. val)(ctx) :=
    collect(pat, val)(ctx U {(x, y)})
  ```
* Bound variable

  ```
  if (x, y) in ctx:
  collect(x, y)(ctx) := {} | {(x, y)}
  ```
* Free variable

  ```
  if (x, _) not in ctx and (_, y) not in ctx
  collect(x, y) := {} | {(x, y}}
  ```
* In any other case, return a unification error

The result is a pair of sets.

Note that union is defined as follows:
```
v1 U ... U vn := v1.left U ... U vn.left | v1.right U ... U vn.right
```

The second curried argument is the context containing the bound variables currently in scope.

Once the collection phase has been executed, we can proceed to the resolution phase.
The goal is to extend the partial assignment to a complete one, using the constraints
that were collected in the previous phase.

```
unify(c_schemas, c_variables) :=

  let result := partial_assignment

  resolve_variables(c_variables)

  while c_schemas is not empty:
    e := the first element such that each argument satisfies `is_solvable` with the keys of the context
    if no such exists, return a unification error

    let (?f, (p1, ..., pn), val, ctx) := e

    if ?f in result:
      TODO
    else:
      greedy_factoring((p1, ..., pn), val, ctx)

  return result

```

The auxiliary functions used are defined below.

```
is_solvable(p)(ctx) := p match
  case f() => true
  case f(p1, ..., pn) => is_solvable(p1) && ... && is_solvable(pn)
  case x if x in ctx => true
  case B x. p0 => is_solvable(p0)(ctx U {x}) 
  case _ => false
```

This function checks whether a pattern can be deterministically compared to a value.

```
greedy_unify((p1, ..., pn), val)(ctx) := val match
  case x if (_, x) in ctx => find i such that (pi, x) in ctx; return xi
  case _ if exists i such that is_same(pi, val) => xi
  case f(a1, ..., an) => f(greedy_factoring(ps, a1)(ctx), ...)
  case B x. v0 => B x. greedy_factoring(ps, v0)(ctx)
  case x if (_, x) not in ctx => x
```

In simpler terms, `greedy_unify` tries to match and bind as many arguments as possible.
This is often (but not always) the desired semantic. In case another solution is desired,
the user is expected to specify explicitly the function definition.

**Examples**

Patterns and values are all formulas; the types of all the symbols should be inferred consequently.

|  #  |     Patterns      |          Values           | Partial assignment  |              Result              |
|:---:|:-----------------:|:-------------------------:|:-------------------:|:--------------------------------:|
|  1  |     `?a /\ b`     |         `c /\ b`          |        `{}`         |         `{?a -> c /\ b}`         |
|  2  |    `?a /\ ?b`     |         `a /\ b`          |     `{?a -> b}`     |           `impossible`           |
|  3  |       `?a`        |         `c /\ b`          |  `{?a -> b /\ c}`   |         `{?a -> b /\ c}`         |
|  4  |       `?a`        |         `?a /\ b`         |        `{}`         |        `{?a -> ?a /\ b}`         |
|  5  |    `?a /\ ?a`     |  `(b \/ c) /\ (c \/ b)`   |        `{}`         |         `{?a -> b \/ c}`         |
|  6  |      `?p(t)`      |          `t = u`          |        `{}`         |       `{?p -> \x. x = u}`        |
|  7  |     `?p(?t)`      |          `t = u`          |        `{}`         |          `unsupported`           |
|  8  |     `?p(?t)`      |          `t = u`          |     `{?t -> t}`     |   `{?p -> \x. x = u, ?t -> t}`   |
|  9  |     `?p(?t)`      |          `t = u`          | `{?p -> \x. x = u}` |   `{?p -> \x. x = u, ?t -> t}`   |
| 10  |   `?p(?t), ?t`    |        `t = u, t`         |        `{}`         |   `{?p -> \x. x = u, ?t -> t}`   |
| 11  |   `?f(?a /\ b)`   |  `(a /\ b) \/ (b /\ a)`   |        `{}`         |          `unsupported`           |
| 12  | `?f(?a /\ b), ?a` | `(a /\ b) \/ (b /\ a), a` |        `{}`         | `{?a -> a, b -> a /\ b, ?f ...}` |
| 13  |     `E x. x`      |         `E y. y`          |        `{}`         |            `{x -> y}`            |
| 14  |   `?f(E x. x)`    |  `(E y. y) /\ (E z. z)`   |        `{}`         |     `{?f -> E y. y, x -> y}`     |

Remarks:
* (1) The solution can be found by doing simple pattern matching.
* (2) The partial assignment makes unification impossible. Note that `{?a -> b, ?b -> a}` would
  still be a valid assignment according to OCBSL, but it is out of the scope of this algorithm.
* (3) The algorithm considers the leaves `c /\ b` and `b /\ c` to be equivalent. Note that by the
  specification, the solution must be a subset of the partial assignment.
* (4) The value `?a` is treated as a constant, it has nothing to do with the pattern `?a`.
* (5) Both `b \/ c` and `c \/ b` are valid assignments for `?a`. The first one is chosen because
  it appears first with respect to the postorder tree traversal.
* (6) There are multiple solutions, so the most general one is chosen.
* (7) The pattern and the partial assignment are too general, `?t` can take any value.
* (8) Reduces to (6).
* (9) Reduces to `?t = u` which has a single solution.
* (10) First `?t` is deduced, then `?p`.
* (11) This case is a limitation of the unifier.
* (12) If the variable `?a` can be resolved, then the argument becomes a constant.
* (13) The bound variable pattern `x` is resolved to the name `y` (name preservation).
* (14) The argument that appears first is used to name `x`.

#### Rule unification

Rules can benefit from the above algorithm, in both backward and forward modes.
The only difference is that not all patterns have a corresponding value to be unified to.
In backward mode we are unifying the conclusion pattern, but the hypotheses do not
have any associated values.

Thus, we should first check whether all the symbols appearing in the non-matchable formulas
but not in the matchable ones are explicitly defined. Then we may apply the unification algorithm
to the matchable formulas and finally resolve all the patterns.
