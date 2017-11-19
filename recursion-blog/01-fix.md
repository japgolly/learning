Let's get started. In order to abstract out recursion, there are three things to do.

1. Make the recursive positions in your data type abstract
2. Create a `Functor` for your data type
3. Wraps your data type in `Fix[_]`

In detail:

## Step 1

Add a type parameter to your data type that will be used to represent recursion
(and other things as you'll see later). Everywhere that your type references
itself, replace the type with the new abstract type parameter.

### `IntList`

Example #1: let's say you have your own hand-written cons-list, specialised to `Int`;
maybe you want to avoid boxing with `List[Int]`. It might look like this:

```scala
// Before
sealed trait IntList
final case class IntCons(head: Int, tail: IntList) extends IntList
case object IntNil extends IntList
```
This type references itself in `IntCons#tail`. Let's fix that...

```scala
//  After (v1)
sealed trait IntList[F]
final case class IntCons[F](head: Int, tail: F) extends IntList[F]
final case class IntNil[F]() extends IntList[F]
```

Ok so now it never references itself, but we've had to modify the non-recursive case,
`IntNil` from an object to a `case class` with zero params.
I'd prefer `IntNil` to remain an object for better ergonomics and efficiency so
let's use variance.

*(Note: A large subset of Scala FP'ers avoid type variance entirely because it's
kind of broken in theory, can lead to bugs in higher-kinded contexts, screws up
implicits sometimes and has breaks type inference sometimes. I advise:
learn about it, and evaluate the tradeoffs for your context and environment.)*

```scala
//  After (v2)
sealed trait IntList[+F]
final case class IntCons[+F](head: Int, tail: F) extends IntList[F]
case object IntNil extends IntList[Nothing]
```

### `BinaryTree`

How about a binary tree with an abstract type `A` in the nodes:

```scala
// Before
sealed trait BinaryTree[+A]
final case class Node[+A](left: BinaryTree[A], value: A, right: BinaryTree[A]) extends BinaryTree[A]
case object Leaf extends BinaryTree[Nothing]
```

Here we replace the left and right branches.

```scala
// After
sealed trait BinaryTree[+A, +F]
final case class Node[+A, +F](left: F, value: A, right: F) extends BinaryTree[A, F]
case object Leaf extends BinaryTree[Nothing, Nothing]
```

Don't worry about preserving the `A` -- don't try to make it an `F[A]` -- just a plain
old `*`-kinded `F` is all you need. The fixpoint types in step 3 ensure that `A`s persist
in both branches' children.

### JSON

JSON is recursive too.

```scala
// Before
sealed trait Json
object Json {
  final case object Null                               extends Json
  final case class  Bool(value: Boolean)               extends Json
  final case class  Str (value: String)                extends Json
  final case class  Num (value: Double)                extends Json
  final case class  Arr (values: List[Json])           extends Json
  final case class  Obj (fields: List[(String, Json)]) extends Json
}
```

Only replace the self references; preserve the outer type.
`List[Json]` should be `List[F]`, not `F`.

```scala
// After
sealed trait Json[+F]
object Json {
  final case object Null                              extends Json[Nothing]
  final case class  Bool  (value: Boolean)            extends Json[Nothing]
  final case class  Str   (value: String)             extends Json[Nothing]
  final case class  Num   (value: Double)             extends Json[Nothing]
  final case class  Arr[F](values: List[F])           extends Json[F]
  final case class  Obj[F](fields: List[(String, F)]) extends Json[F]
}
```


## Step 2

In this step we create a `Functor` for our data types.
`Functor` is a type class that exists in the FP lib of your choice, namely
Scalaz or Cats. It looks like this:

```scala
trait Functor[F[_]] {
  def map[A, B](fa: F[A])(f: A => B): F[B]
}
```

It empowers the world outside your data structure to change one of its abstract
types, and by necessity, all values of that type. It's just like calling `.map` on a list:

```scala
// Change the values
List(1, 2, 3).map(_ * 10)
  // yields
  List[Int](10, 20, 30)

// Change the type too
List(1, 2, 3).map(i => s"[$i]")
  // yields
  List[String]("[1]", "[2]", "[3]")
```

This functor is how the generic recursion abstractions can have access to, and
control over the recursive spots in your data.

*(Note: If you want to use monadic variants of morphisms later, you'll need to
upgrade your Functor to a Traverse. I'll show that in a future post but just
keep it in mind.)*

Let's create instances for our examples above.
I'll be using Scalaz here; to use Cats instead, only the imports need to change and
the code itself is identical.

### `IntList`

Let the compiler guide you, it will only accept one implementation:

```scala
implicit val functor: Functor[IntList] = new Functor[IntList] {
  override def map[A, B](fa: IntList[A])(f: A => B): IntList[B] = fa match {
    case IntCons(head, tail) => IntCons(head, f(tail))
    case IntNil              => IntNil
  }
}
```

### `BinaryTree`

As intended, this next case introduces a bit more complexity.
We want to provide the ability to transform the recursive positions which means
we need to keep the `value: A` position abstract and stable.

You'll need to use [kind-projector](https://github.com/non/kind-projector)
to get the nice `BinaryTree[A, ?]` syntax, instead of the monsterous,
out-of-the-box `({ type L[X] = BinaryTree[A, X] })#L` syntax.

```scala
implicit def functor[A]: Functor[BinaryTree[A, ?]] = new Functor[BinaryTree[A, ?]] {
  override def map[B, C](fa: BinaryTree[A, B])(f: B => C): BinaryTree[A, C] = fa match {
    case Node(left, value, right) => Node(f(left), value, f(right))
    case Leaf                     => Leaf
  }
}
```

There's nothing special about the `F` type over the `A`. You could also write a
functor over the `A` type, i.e. a `Functor[BinaryTree[?, F]]` instance.
Because of the way Scala implicits work, you can only make one implicit.
It's got nothing to do with recursion. Actually, further discussion is out-of-scope here,
but maybe just be aware, think about if that would be a problem for you, and how you might handle it.

### JSON

Here our `F`s are embeded in other values so we have to work a little harder to
transform them. Lists have functors too so it's easy peasy: just call `.map`.

```scala
implicit val functor: Functor[Json] = new Functor[Json] {
  override def map[A, B](fa: Json[A])(f: A => B): Json[B] = fa match {
    case Null         => Null
    case j: Bool      => j
    case j: Str       => j
    case j: Num       => j
    case Arr (values) => Arr(values.map(f))
    case Obj (fields) => Obj(fields.map { case (k, v) => (k, f(v)) })
  }
}
```

## Step 3. Fixpoint

In step 1, we went from a recursive data structure to a non-recursive data structure.
Our goal is to be able to abstract over/away recursion, not to vanquish it.
How do we regain our recursion?
We still want the users of our amazing `IntList` library to be able to store
more than one element after all.

We've going to wrap our types in a magical fixpoint type.
Doing so will give us back our recursion.

Here's a definition of Fix:
```scala
case class Fix[F[_]](unfix: F[Fix[F]])
```

Confused? This isn't a theory series but get a pen and paper, plug in `IntList` and expand the alias step-by-step; it'll clear it up real quick.

Exciting side note: [Stephen Compall](https://twitter.com/S11001001) and [Tomas Mikula](https://twitter.com/tomas_mikula) found a way to define `Fix` without boxing!
See [how, here](https://github.com/scalaz/scalaz/pull/1472/files).
I measured a [20-30% improvement](https://github.com/japgolly/microlibs-scala/commit/c2c1f8adaa9c9166ed6c10a0c3c09cfdbc0c8d58) and copied the approach in [my own recursion library](https://github.com/japgolly/microlibs-scala/tree/master/recursion).
Very awesome stuff.

Anyway, wrap your data types in `Fix[_]` and you get your recursion back.

```scala
import japgolly.microlibs.recursion.Fix

type RecursiveIntList       = Fix[IntList]
type RecursiveBinaryTree[A] = Fix[BinaryTree[A, ?]]
type RecursiveJson          = Fix[Json]
```

...which is a bit long-winded and unpleasant.
Let's rename things.

The most-common convention I've seen is to append an `F` for "functor" to the
data type and use the proper name in the alias.

```scala
sealed trait IntListF[+F]
type IntList = Fix[IntListF]

sealed trait BinaryTreeF[+A, +F]
type BinaryTree[A] = Fix[BinaryTreeF[A, ?]]

sealed trait JsonF[+F]
type Json = Fix[JsonF]
```

This actually works out great because then, in practice, I often create a new
object with helpers that improve ergonomics and avoid `Fix` boilerplate when you
need to manually create a structure, for example, unit test expectations, using
a parser that doesn't play nice with recursion schemes.

For example:
```scala
type IntList = Fix[IntListF]

object IntList {

  // Helpful cos Scala's type inference fails so often
  def apply(f: IntListF[Fix[IntListF]]): IntList =
    Fix(f)

  def nil: IntList =
    apply(IntNil)

  def cons(head: Int, tail: IntList): IntList  =
    apply(IntCons(head, tail))

  def fromList(is: Int*): IntList  =
    is.foldRight(nil)(cons)
}
```

# Done!

That's it! We're done.
It may seem like a lot of work but there's benefit coming that greatly outweighs
the cost.
