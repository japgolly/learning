PL evolution and resistence
past: machine code --> asm --> C  etc
now: types & FP
future: dep types, effects

----

----

(?)
Types are not a nice feature to opt-in to.
Address arguments of dyn-typed langs head on.
(-) no.
Find arguments for dyn-langs
Counter each without mentioning the original arg

----

* FP  ?
  * Immutability
  * Referential transparency
  * Equational reasoning
  * Pure vs impure
  * Unsafe Scala ops

* Parametricity
  * Benefits (theorems, precision: type capability, reuse 
  * How
  * Examples

---------------------------------------------------------------------------------

* Relation to Logic
  * Curry-Howard Isomorphism
  * Each order of logic + corresponding types
  * requires purity

* Types vs Tests 

* Benefit = ?
  * Fail-fast program-wide. Speed/size = huge
  * Intent/algo expressiveness/encoding
    * Tooling more capable
    * Confidence in correctness
    * Communication between devs (=doc)
    * Safe & easy refactoring

* Parametricity (briefly)
  * Abstraction = precision

* Type inhabitant math
  * Holes
    * Differentiate
    * Zippers
 

Compare `a -> Unit` being 1ᵃ, and `A → True` simplifying to `A`.

There's only 1 reasonable fn from `A -> Unit`.
Casting to `A: Unit` is actually: `(A ∨ ¬A) -> True`

Anything else is actually: `A -> SideEffect : Unit`
Which means, ignoring purity, from the compilers PoV: `(SideEffect ∨ ¬SideEffect) → True` = "succeed or crash, I don't care"

We want software to work. We don't want it to crash.
Do we really know better than the compiler?
Maybe when we're writing new code, of course we usually think we are, but what about a few hours later, what about by other team members, or after a big refactoring.
Side-effect free code is really easy nowadays. The tools are here.
Parts of the industry that use them have a competitive advantage.
It's a learning curve, so was OO to C programmers, so was C to asm programmers, so was asm to machine-code writers.

Property testing

encode usage constraints
  - cannot save X to DB until user has logged in
    DAO split into pub/pri, require authtoken to get pri (highlight that authtoken isn't used)

* Examples
  * Non-emptyness
  * primitive wrapping (eg. stringly typed)
  * don't use bools
  * Thinking in logic before code = more testable (sigs), accurate
  * types are cheap - ShipReq FilterAst vs FilterSpec
  * `IMap` preserving relationships between keys and values
  * correction & validation - from logic to types -- if all types are the same (String,String,String) it doesn't matter, we still prove that correction happens first
  * SignalType.AndInput --- ∀ s ∈ SignalType. ∃ t : s accepts t


---------------------------------------------------------------------------------

# Logic

True
False
A
A ∧ B
A ∨ B
A → B
A ↔ B
¬ A

∃
∀

Set theory
A ∈ B

---------

Types = propositions
Successful compilation (program) = proof

Inhabitant. Value.


---------


True
`Unit` (`Any`)

False
`Nothing`

A
`A`

A ∧ B
`(A, B)`
`A with B`

A ∨ B
```scala
sealed trait A∧B
case object A extends A∧B
case object B extends A∧B

// Scala stdlib
Either[A, B]

// Scalaz
A \/ B

// Cats
A Xor B

// Scala 3 aka Dotty
A | B
```
A ∨ B = ¬(¬A ∧ ¬B)


A → B
```scala
A => B

def ab(a: A): B
```

A ↔ B
(A → B) = (B → A)
{(A → B) ∧ (B → A)} ∨ {¬(A → B) ∧ ¬(B → A)}
```scala
type Not[X] = X => Nothing
(A => B, B => A) \/ (Not[A => B], Not[B => A])
```

¬ A
A → False
```scala
A => Nothing
```

∀


∃

∈


-----

¬¬A
¬¬A = A
```scala
(A => Nothing) => Nothing
```

---------

type-level different than value-level
* type-level
  * ∧ = `with`
  * ∨ = ¬(¬A ∨ ¬B)
  * A→B = `A <: B`
  * ¬ = `A => Nothing`
  * ↔ = `=:=`
  * `type ∃[P[_]] = P[T] forSome { type T }`
  * `type ∀[P[_]] = ¬[∃[({ type λ[X] = ¬[P[X]]})#λ]]`
  
* value-level
  * ∧ = `Tuple2`
  * ∨ = `Either`
  * A→B = `A => B`
  * ¬ = ???
  * ↔ = ???

---------

Falseness is very rarely what we want in our code.
It's nearly always creating propositions that embody and enforce our intent.

I've reached for falsity a few times but the only instance I can remember:

`A` ≠ `Future[_]`
```scala
sealed trait NotAFuture[A]
object NotAFuture {
  implicit def notAFuture[A]: NotAFuture[A] = null
  implicit def itsAFuture1[A]: NotAFuture[Future[A]] = null
  implicit def itsAFuture2[A]: NotAFuture[Future[A]] = null
}
```

```scala
object Glue {

  def apply[A: NotAFuture](a: ⇒ A): Glue[A] =
    liftF(s ⇒ {
      import s.ec
      Future(a)
    })

  def future[A](future: ⇒ Future[A]): Glue[A] =
    liftF(_ ⇒ future)

  private[Glue] def liftF[A](fn: State ⇒ Future[A]): Glue[A] =
    ...
```

```scala
  def apply[A: NotAFuture](a: ⇒ A)
  def apply[A            ](a: ⇒ A)(implicit ev: NotAFuture[A])
```


Break problems into smaller problems, turn small problems into small solutions, compose solutions

a&b -> {a,b}

a=>b ∧ a
---------
b

-----

What is falseness? Let's find out...
False = `Nothing`

def/val/anon?

```scala
def falsity: Nothing =
  // how do we make this compile?
```
```scala
def falsity: Nothing =
  // how do we make this compile?
```
```scala
def falsity: Nothing =
  // how do we make this compile?
```
```scala
def falsity: Nothing =
  1 // Compilation error: type mismatch
```
```scala
def falsity: Nothing =
  throw new RuntimeException("FALSE!!")
```
```scala
def falsity: Nothing =
  sys.error("FALSE!!")
```
```scala
def falsity: Nothing =
  ???
```

Now we have a false proposition in our code. If we try to use/depend-on/eval, boom.

We don't want falsity in our programs. Falsity means crashing.
With types, by success of compilation we can prove our program will work(1) and is correct(2).
Possible errors are still:
1) Resources (memory, stack)
2) Logic bugs if our types aren't expressive enough and/or logic is value-dependant (eg. sorting in wrong direction)


¬A
A -> Nothing (when A)
(a=false) = Nothing -> Nothing = True


Intuitionist logic

Casting things to `Unit` is the equivalent of forcing propositions to True.

define isomorphism

"This statement is not provable."

termination proven in typed lambda calc, undecidable in untyped

props = types
proofs = programs
normalisation of proofs = program evaluation

define iso

traits!! Can't abstract.
Use case class + fns
