Laws / Properties / Axioms
==========================

* Closure: Return type matches input type.
  ✓ f(Int, Int): Int
  ✖ f(Int, Int): String

* Associativity: Adjacent operations can be performed in any order.
  (a⋅b)⋅c = a⋅(b⋅c) = a⋅b⋅c

* Commutativity: Argument order doesn't matter.
  a⋅b = b⋅a

* Identity.
  ∃e∈M : ∀a∈M : e⋅a = a = a⋅e

* Invertability: Each element has an inverse/negative.
  ∀a∈M : ∃b∈M : a⋅b = e = b⋅a

* Idempotence
  a⋅a = a

* Distribution
  Left  - x·(y + z) = (x·y) + (x·z)
  Right - (y + z)·x = (y·x) + (z·x)

* Absorption identity
  a = a∨(a∧b)
  a = a∧(a∨b)


Structures
==========

### Set M and single binary operation (⋅)

* Magma
  Combines two elements into same type. M × M → M
  ∀a,b ∈ M : a⋅b ∈ M

* Semigroup
  A magma where ⋅ is associative.

* Monoid
  A semigroup with identity.

* Quasigroup
  A magma with invertability.
  ∀b∈M : ∃a,c∈M : a⋅b = b⋅c

* Loop
  A quasigroup with identity.

* Group
  A monoid with invertability.
  A loop with associativity.

* Abelian Group
  A group with commutativity.

* Semilattice
  A semigroup with idempotence and commutativity.

### Set M and two binary operations

* Ring
  Operations typically called + and ⋅.
  + is an Abelian Group.
  ⋅ is associative and distributes over +.
  ⋅ has identity. [Arguable]

* Lattice
  M is partially-ordered.
  Operations called ∧ (meet) and ∨ (join).
  Has absorption identity.



Other
=====

### Glossary

* Partial vs Total function
  Non-exhaustive pattern match vs exhaustive.
  f(X):Y maps some vs all Xs to Ys.

* Partially-ordered set
  Elements of the set are comparable, have an Ordering.
  The ≤ operator is possible.


### Number Systems

* ℕ - Natural    - Positive integers (0 arguable)
* ℚ - Rational   - Fractions. x/y
*     Irrational - Decimal that can't be expressed as x/y.
* ℝ - Real       - Any decimal.
