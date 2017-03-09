# Algebras and Fixpoints
---
# S ⇒ (S, A)
---
# F A ⇒ A
---
# F[A] ⇒ A
---
# Recursive Data

What is it?

##### My use cases over the last few years
  * ShipReq: filter expr
  * ShipReq: tags M:M
  * ShipReq: use case tree
  * ShipReq: code trie
  * Nyaya: Properties
  * TestState
  * Sprockets: Expr
  * More?
---
# Recursive Data

#### Why is it important?
  * Model reality
    * My friends have friends who have friends who have friends...
    * FS: directories have directories which have directories...
  * Efficiency (time) - maps
  * Efficiency (space) - tries
---
# Recursion

Not only about data, can also use existing iterable types.
  * String processing
  * List processing
---
# Recursive Data: Example

```
sealed trait Calc
case class Number  (i: Int)           extends Calc
case class Add     (a: Calc, b: Calc) extends Calc
case class Multiply(a: Calc, b: Calc) extends Calc

// 1 + 2
Add(
  Number(1),
  Number(2))

// 3 * (1 + 2)
Multiply(
  Number(3),
  Add(
    Number(1),
    Number(2)))
```

---
# Problem #1

### No control over the recursion.
### It's hardcoded.
### Can't abstract, define depth.
---
# Problem #2

### Recursion is usually hard. Often requires practice.
### Non-recursion easier than recursion.
---
# Problem #3

Can't annotate sub-nodes.

#### No annotations
```scala
case class PersonUnsaved(name: String,
                         age: Int,
                         friends: List[PersonUnsaved])
```
#### Annotate with ID
```scala
case class PersonId(value: Long) extends AnyVal

case class Person(id     : PersonId,
                  name   : String,
                  age    : Int,
                  friends: List[Person])
```
---
# Problem #3
#### Annotate `Calc` with logging
```scala
sealed abstract class Calc(val log: String)

case class Number(i: Int)
  extends Calc(i.toString)

case class Add(a: Calc, b: Calc)
  extends Calc(s"(${a.log} + ${b.log})")

case class Multiply(a: Calc, b: Calc)
  extends Calc(s"(${a.log} * ${b.log})")
```
---
# Problem #3
#### Annotate `Calc` with whatever
```scala
sealed abstract class Calc[A] {
  val ann: A
}

case class Number  [A](ann: A, i: Int)                 extends Calc[A]
case class Add     [A](ann: A, a: Calc[A], b: Calc[A]) extends Calc[A]
case class Multiply[A](ann: A, a: Calc[A], b: Calc[A]) extends Calc[A]

// 3 * (1 + 2)
Multiply("3 * (1 + 2)",
  Number("3", 3),
  Add("(1 + 2)",
    Number("1", 1),
    Number("2", 2)))
```
---
# Problems #4 ~ #23

So obvious that we don't even need to talk about them.

*(is joke)*

---
# Q: How do we deal with this?

A: Generalise the recursive-type.
```scala
// No longer recursive.

sealed trait Calc[A]

case class Number  [A](i: Int)     extends Calc[A]
case class Add     [A](a: A, b: A) extends Calc[A]
case class Multiply[A](a: A, b: A) extends Calc[A]
```
`Calc` no longer references `Calc`.
Notice `Add`/`Multiply` fields.

---
# Wait...

```scala
val WHY_YOU_NO_WORK_?! : Calc[Calc] =
  Multiply(
    Number(3),
    Add(
      Number(1),
      Number(2)))
```
---
# Type constructors
* `List`
* `Map`
* `Future`

# Types
* `Unit`
* `List[Int]`
* `Map[Int, String]`
* `Future[List[Int]]`

---
# Type constructors
* `Functor`
```scala
trait Functor[F[_]] {
  def map[A, B](fa: F[A])(f: A => B): F[B]
}
```

# Types
* `Functor[List]`
```scala
object ListFunctor extends Functor[List] {
 override def map[A, B](list: List[A])(f: A => B): List[B] =
   list.map(f)
}
```
---

# Type constructors
* `Calc`

# Types
* `Calc[Unit]`
* `Calc[List[Int]]`
* `Calc[Nothing]`
* `Calc[Calc[Nothing]]`
* `Calc[Calc[Calc[Nothing]]]`
* `Calc[Calc[Calc[Calc[Nothing]]]]`
* `Calc[Calc[Calc[Calc[Calc[Nothing]]]]]`
---
This works but isn't nice.
```scala
val MAX_DEPTH_3 : Calc[Calc[Calc[Nothing]]] =
  Multiply(
    Number(3),
    Add(
      Number(1),
      Number(2)))
```
---
# Fixpoints!

```scala
final case class Fix[F[_]](unfix: F[Fix[F]])
```
---
# Fixpoints!

```scala
final case class Fix[F[_]](unfix: F[Fix[F]])
```
```scala
type RecursiveCalc = Fix[Calc]
//                 = Fix[Calc[Fix[Calc[Fix[Calc[Fix[Calc[...
```

```scala
val UNLIMITED_DEPTH_! : RecursiveCalc =
  Fix(Multiply(
    Fix(Number(3)),
    Fix(Add(
      Fix(Number(1)),
      Fix(Number(2))))))
```
---
# How? Why?
It goes back and forth.
```scala
def gimmeFix(c: Calc[Fix[Calc]]): Fix[Calc] =
  Fix[Calc](c)

def gimmeCalc(f: Fix[Calc]): Calc[Fix[Calc]] =
  f.unfix
```
```q
    Fix[Calc]

      |  ↑
unfix |  | Fix
      ↓  |

  Calc[Fix[Calc]]
```
---
```scala
val calc: Fix[Calc] =
  Fix(Number(1))
```
```scala
val calc: Fix[Calc] =
  gimmeFix(
    gimmeCalc(
      gimmeFix(
        gimmeCalc(
          gimmeFix(
            gimmeCalc(
              gimmeFix(
                gimmeCalc(
                  gimmeFix(
                    Number(1))))))))))
```
---
# ALL YOU NEED TO KNOW IS:
* Generalise (use an `A`) in place of a self-reference.
* Use a library like Matryoshka, or copy-and-paste `Fix`.
* Wrap your stuff in `Fix` when you want recursion.

---
# Algebra

## `F A -> A`

```scala
type Algebra[F[_], A] = F[A] => A
```
---
```scala
type Algebra[F[_], A] = F[A] => A
```
```scala
val listSum: Algebra[List, Int] =
  _.sum

def listSumMethod(list: List[Int]): Int =
  list.sum

val listSumMethodAsAlgebra: Algebra[List, Int] =
  listSumMethod
```
---

# Ok... and?

A special function exists...

```scala
def awesome[F[_]: Functor, A](alg : Algebra[F, A],
                              data: Fix[F]): A
```

Like magic!
No `A` in `Fix[F]`.

---
# Let's try it out!
---

### Well, first there's a prerequisite:

```scala
implicit val functor: Functor[Calc] =
  new Functor[Calc] {
    override def map[A, B](c: Calc[A])(f: A => B): Calc[B] =
      c match {
      
        case Number  (i)    => Number  (i)
        case Add     (a, b) => Add     (f(a), f(b))
        case Multiply(a, b) => Multiply(f(a), f(b))
        
      }
  }
```
---
# Let's try it out!
```scala
val eval: Algebra[Calc, Int] = {
  case Number  (i)    => i
  case Add     (a, b) => a + b
  case Multiply(a, b) => a * b
}
```
---
```scala
val c: Fix[Calc] = ...
```
```scala
def awesome[F[_]: Functor, A](alg : Algebra[F, A],
                              data: Fix[F]): A

val eval: Algebra[Calc, Int] = {
  case Number  (i)    => i
  case Add     (a, b) => a + b
  case Multiply(a, b) => a * b
}

awesome(eval, c) // returns 9
```
---
```scala
val explain: Algebra[Calc, String] = {
  case Number  (i)    => i.toString
  case Add     (a, b) => s"($a + $b)"
  case Multiply(a, b) => s"($a * $b)"
}
```
---

```scala
val explain: Algebra[Calc, String] = ...
val eval   : Algebra[Calc, Int]    = ...

val explainAndEval: Algebra[Calc, (String, Int)] =
  explain zip eval

awesome(explainAndEval, c) // returns ("3 * (1 + 2)", 9)
```
---
# Amazing!
Real name is catamorphism.
It goes to the ends of a tree, then calculates it way back up.
Bottom-up.

---
What is this black magic?
This heresay?
"Lies!"
# Proof that it works...
---
```q

    Fix[Calc]

      |  ↑
unfix |  | Fix
      ↓  |

  Calc[Fix[Calc]]
  
```
---
```q
                      cata = ???
    Fix[Calc]      - - - - - - - ->  A

      |  ↑
unfix |  | Fix
      ↓  |

  Calc[Fix[Calc]]

```
---
```q
                      cata = ???
    Fix[Calc]      - - - - - - - ->  A

      |  ↑
unfix |  | Fix
      ↓  |

  Calc[Fix[Calc]]  --------------->  Calc[A]
                    calc.map(cata)
```
---
```q
                      cata = ???
    Fix[Calc]      - - - - - - - ->  A

      |  ↑                           ↑
unfix |  | Fix                       | alg: Algebra[Calc, A]
      ↓  |                           |

  Calc[Fix[Calc]]  --------------->  Calc[A]
                    calc.map(cata)
```
---
```q
                         cata
    Fix[Calc]      - - - - - - - ->  A

      |  ↑                           ↑
unfix |  | Fix                       | alg: Algebra[Calc, A]
      ↓  |                           |

  Calc[Fix[Calc]]  --------------->  Calc[A]
                    calc.map(cata)
```
```scala
def cata: Fix[Calc] => A =
  fix => {
    val calc : Calc[Fix[Calc]] = fix.unfix
    val calcA: Calc[A]         = calc.map(cata)
    val a    : A               = alg(calcA)
    a
  }
```
---
```q
                        cata
    Fix[Calc]      - - - - - - - ->  A

      |  ↑                           ↑
unfix |  | Fix                       | alg
      ↓  |                           |

  Calc[Fix[Calc]]  --------------->  Calc[A]
                    calc.map(cata)
```

```scala
def cata[F[_], A](alg: Algebra[F, A])(f: Fix[F])
                 (implicit F: Functor[F]): A =
  alg(F.map(f.unfix)(cata(alg)))
```
---
```q
                        cata
    Fix[Calc]      - - - - - - - ->  A

      |  ↑                           ↑
unfix |  | Fix                       | alg
      ↓  |                           |

  Calc[Fix[Calc]]  --------------->  Calc[A]
                    calc.map(cata)
```

```hs
cata :: Functor f => (Algebra f a) -> Fix f -> a
cata alg = alg . fmap (cata alg) . unfix

```
---
# ALL YOU NEED TO KNOW IS:
* Use a library like Matryoshka, or copy-and-paste `Algebra` and `cata`.
* Create an algebra when you want to fold/reduce a tree.
* Call `cata`. *Done!*

---
# Next up: CoAlgebras
---
Everything in category theory can have its arrows reversed - this is called a dual.

### Monad
* `M[A] => (A => M[B]) => M[B]`
### CoMonad
*   `W[B] => (W[B] => A) => W[A]`
---
### Algebra:
  * `F[A] => A`
### CoAlgebra
  * `A => F[A]`

---
# What's the purpose?

```scala
type CoAlgebra[F[_], A] = A => F[A]
```
```scala
val factors: CoAlgebra[Calc, Int] = int =>
  if (int > 2 && int % 2 == 0)
    Multiply(2, int / 2)
  else
    Number(int)
```
---
# Another magic function
```scala
def emosewa[F[_]: Functor, A](alg : CoAlgebra[F, A],
                              data: A): Fix[F]
```
Notice, there's no `A` in the result.

---
Real name is anamorphism.

Dual of catamorphism.
```hs
cata: Fix f -> Alg   f a -> a
ana : a     -> CoAlg f a -> Fix f
```

It starts with the at the top, then calculates its way down until the tree is complete.
Top-down.

The `A` is an instruction/description of the subtree yet to be calculated.

---
# ALL YOU NEED TO KNOW IS:
* Use a library like Matryoshka, or copy-and-paste `CoAlgebra` and `ana`.
* Create a coalgebra when you want to build up a tree with context.
* Call `ana`. *Done!*

---
# There is no more.
No new information required.
# There is more.
There are a bunch of variations and combinations that extend/build on what you've now learned.

---
![center](algebras.png)

---
![center](recursion-schemes.png)

---
# Map Fusion
Build-up & tear-down in one pass.

Generate & consume without actually creating the whole tree.

---
# Monadic variants

```scala
type AlgebraM  [M[_], F[_], A] = F[A] => M[A]

type CoAlgebraM[M[_], F[_], A] = A => M[F[A]]

```

```scala
val eval: Calc[Int] => String \/ Int = {
  case Num(i)    => \/-(i)
  case Div(_, 0) => -\/("Division by zero detected. ABORT!")
  case Div(a, b) => \/-(a / b)
}
```
```scala
// Calc[Int] => String \/ Int
// F   [A]   => M         [A]

AlgebraM[String \/ ?, Calc, Int]
//       ^^^^^^^^^^^  ^^^^  ^^^
//       M            F     A
```
---
# Real Example

---
# Random Data

Generating random data is important.

It's the secret sauce of property testing that ensures that, (asymptotically), you test your code with every possible, legal or desriable value.

Also useful for:
* load testing
* stress testing
* benchmarking (if gen supports determinism)

---
# Nyaya
```scala
case class Example(enabled : Boolean,
                   position: (Int, Int),
                   stuff   : Map[Long, Option[String]])

val g: Gen[Example] =
  for {
    e <- Gen.boolean
    p <- Gen.chooseInt(-128, 128).pair
    s <- Gen.ascii.string(1 to 10).option
           .mapBy(Gen.long)(0 to 4)
  } yield Example(e, p, s)
  
val example: Example = g.sample()

// Example(
//   true,
//   (-30,83),
//   Map(2340946662719216224 -> Some(!\@91u),
//       7161527918171176759 -> None))

```
---
# DSL
```scala
sealed trait Expr[+A]

case class Literal(typeAndValue: Type.AndValue) extends Expr[Nothing]
case class Proposition[A](op: BoolOp, left: A, right: A) extends Expr[A]
case class Arithmetic[A](op: ArithmeticOp, left: A, right: A) extends Expr[A]
case class Comparison[A](op: ComparisonOp, left: A, right: A) extends Expr[A]
case class Not[A](expr: A) extends Expr[A]
case class ReadState(name: String) extends Expr[Nothing]
case class CallBuiltInFunction[A](name: String, args: List[A]) extends Expr[A]
```
---
# Goal

```scala
def gen: Gen[Fix[Expr]] =
  ???
```
---
```scala
def gen: Gen[Fix[Expr]] =
  ???

val coalgebra: CoAlgebra[Expr, ?] =
  ???
```
---
```scala
/** Specification for how a valid expression should be generated. */
case class ExprSpec(
  resultType      : Type,
  remainingDepth  : Int)

val coalgebra: CoAlgebraM[Gen, Expr, ExprSpec] =
//           : ExprSpec => Gen[Expr[ExprSpec]] =
  spec => ???

def gen(result: Type, maxDepth: Int = 5): Gen[Fix[Expr]] =
  anamorphismM(coalgebra)(ExprSpec(result, maxDepth))
```

---

```scala
val coalgebra: CoAlgebraM[Gen, Expr, ExprSpec] = { spec ⇒
  var gens = List.empty[Gen[Expr[ExprSpec]]]
  
  // Add non-recursive gens
  gens ::= genLiteral(spec.resultType)
  // ...

  // Add recursive gens
  if (spec.remainingDepth > 0) {
    val nextDepth = spec.remainingDepth - 1
    
    resultType match {
      case Type.Bool ⇒
        val boolSpec = Spec(Type.Bool, nextDepth)
        gens ::= Gen pure Not(boolSpec)
        
        val longSpec = Spec(Type.Long, nextDepth)
        gens ::= genComparisonOp.map(op =>
                   Comparison(op, longSpec, longSpec))
      
      // case ... => ...
    }
  }
    
  Gen.chooseGen(gens) // returns a Gen[Expr[ExprSpec]]
}
```
---
I don't think about recursion.

Where there'd normally be recusion, I just declare what I want.

# Magic ensures.

---

# Summary [1/2]

* Allows you to not think about recursion or implement it.

* Allows you to write code that works with *ANY* structure.
  * eg. generic algebras for size & height.

* You don't need to be a pilot to catch a flight. You don't need to understand Greek or category theory to use this.

* It wasn't discovered simply but now that it is, it's simple to use.
---
# Summary [2/2]

# ALL YOU NEED TO KNOW IS:
* Use a library or copy-and-paste little snippets that you need. They're tiny.
* Parametise and use `Fix` instead of self-referencing.
* When writing your logic, use plain old functions--just use the right shapes.
* **PROFIT.**

---

# Resources
* Matryoshka: Scala library by Slamdata.
* Youtube: Any talks by Greg Pfeil.
* Youtube: "Pure functional database programming with fixpoint types" by Rob Norris.
* Google: recursion scheme cheatsheets
* Paper: "Functional Programming with Bananas, Lenses, Envelopes and Barbed Wire"
