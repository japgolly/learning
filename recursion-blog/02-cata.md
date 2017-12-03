Recursion schemes are awesome, and practical.
This is chapter 2 in a [series of blog posts about recursion schemes](https://github.com/japgolly/learning/tree/public/recursion-blog).
This series uses Scala, and will focus on usage and applicability.
It will be scarce in theory, and abundant in examples.
The theory is valuable and fascinating, but I often find that knowing the theory alone is only half understanding.
The other half of understanding comes from, and enables, practical application.
I recommend you bounce back and forth between this series and theory.
The internet is rich with blogs and videos on theory that explain it better than I would, so use those awesome resources.

## Before you start...

If you don't know what I mean by any of the following,
read or skim [chapter 1 of this series](https://japgolly.blogspot.com/2017/11/practical-awesome-recursion-ch-01.html).

* `Fix[_]`
* `IntList` / `IntListF[_]`
* `BinaryTree` / `BinaryTreeF[_]`


This series doesn't depend on, or emphasise, Matryoshka or any other library.
If you'd like to understand why, I've explained [here in the FAQ](TOOODOOOO).

# The Catamorphism

What is a catamorphism?
It can be answered from a few perspectives.

### What

It's often referred to as a fold over your data structure.
Examples that sum or count values are very common.
An example of the concept straight of out Scala stdlib would be
`List(1, 3, 7).foldLeft(0)(_ + _) == 11`.
As you'll see below, folds and catamorphisms are capable of much more than calculating numbers.

The definition of catamorphism is:

```scala
def cata[F[_]: Functor, A, B](fAlgebra: F[A] => A)(f: Fix[F]): A =
  fAlgebra(f.unfix.map(cata(fAlgebra)))
```

The first argument `fAlgebra` is so-called because `F[A] => A` is known as an
F-algebra. *What* it is, is your folding-logic function that inspects a single
level/layer of your structure without recursion.
The `f: Fix[F]` is the data structure that you want to fold into some type `A`.
Combine the two with this magic function and all the recursion is taken care of
for you, and the result is just a single `A`. If you're confused, the examples
below will clear it up.

Level? Layer? Visualise your recursive data types like this:
```
IntList
=======

This is equivalent to List(1, 2, 3, 4, 5).

IntCons(1, _) ← Level 1
IntCons(2, _) ← Level 2
IntCons(3, _) ← Level 3
IntCons(4, _) ← Level 4
IntCons(5, _) ← Level 5
IntNil        ← Level 6
```

```
BinaryTree
==========

      Branch(_, "root", _)          ← Level 1
              |
  +-----------+-----------+
  |                       |
Leaf      Branch(_, "right", _)     ← Level 2
                 |           |
               Leaf         Leaf    ← Level 3
```

### How

Look at the above definition.
There's an interesting note about parametricity. The only means it
has of producing an `A` is to call `fAlgebra`... which requires an `F[A]`...
so how do you put an `A` in the `F[_]` if you can't produce `A`s?
Remember that the hole if `F[_]` represents the recursive case?
In non-recursive cases (eg. `Nil` in a cons list) the type is a phantom-type,
completely unused, or covariant and always `Nothing`. For example:

```scala
case class Eg[T](int: Int)

def changeIt[X, Y](eg: Eg[X]): Eg[Y] =
  Eg(eg.int)
```

When a type variable is unused you can replace it with anything you want,
which is exactly what happens in `Functor[F]`.

It's also important to understand the order in which things happen.
Catamorphisms:

1. start at the root (their input, the `f: Fix[F]`)
2. (computationally) move to the leaves
3. calculate their way back to the root

Which means your folding logic is going to start executing against all the leaves
first, then their parents, then *their* parents, etc.
(When we get to some of the more advanced morphisms, understanding the order becomes critical.)


### Optimisation

I did say that this is a practical series.
This is a good a place as any to mention that this definition, while correct,
is inefficient.

Every time it recurses it has to create the same functions with the same logic
over and over again. We can make it more efficient by creating what we need once
and reusing it.

```scala
def cata2[F[_], A, B](algebra: F[A] => A)(f: Fix[F])(implicit F: Functor[F]): A = {
  var self: Fix[F] => A = null
  self = f => algebra(F.map(f.unfix)(self))
  self(f)
}
```

In this new definition, we create the recursive function once and reuse it.
Despite the null, it's 100% safe because we (provably) set it before it's used.

Let's measure it. How fast does it perform in comparison to the original?
105%? 110%?

```scala
[info] Benchmark         (size)  Mode  Cnt    Score   Error  Units
[info] RecursionBM.cata      10  avgt   10    0.274 ± 0.003  us/op
[info] RecursionBM.cata2     10  avgt   10    0.146 ± 0.001  us/op
[info] RecursionBM.cata     100  avgt   10    2.323 ± 0.020  us/op
[info] RecursionBM.cata2    100  avgt   10    1.555 ± 0.006  us/op
[info] RecursionBM.cata    1000  avgt   10   31.111 ± 0.720  us/op
[info] RecursionBM.cata2   1000  avgt   10   16.067 ± 0.187  us/op
[info] RecursionBM.cata   10000  avgt   10  326.443 ± 9.054  us/op
[info] RecursionBM.cata2  10000  avgt   10  165.470 ± 1.617  us/op
```

200%, it's twice as fast!
Not bad for a tiny bit of one-off, hidden boilerplate.

*Side-note: I ran the benchmark on a i7-6700HQ and all results are under 1ms,
even at structure size of 1x10000 (length x depth), which means that either
implementation is going to be fine on a fast CPU in a non-high-throughput
solution. It'd be interesting to know what the measurements would be in prod,
on real GCP/AWS VMs; the savings of the optimisation would be more significant
because the VCPUs are slower.*


### F-Algebras

This isn't necessary but I'm also going to add a type alias.

```scala
type Algebra[F[_], A] = F[A] => A
```

and tweak the catamorphism definition to

```scala
def cata2[F[_], A, B](algebra: Algebra[F, A])(f: Fix[F])(implicit F: Functor[F]): A = {
  var self: Fix[F] => A = null
  self = f => algebra(F.map(f.unfix)(self))
  self(f)
}
```

Type aliases don't exist at runtime, the compilation process dealiases them completely.
You can also use either definition interchangably.

```scala
def useAlias[F[_], A](f: F[A] => A): Algebra[F, A] =
  f

def removeAlias[F[_], A](f: Algebra[F, A]): F[A] => A =
  f
```

There are two advantages to having and using a type alias.
1. Readability. The `A` and the `F` are separated; the `A` doesn't repeat; it clarifies intent the more you get used to recursion schemes.
2. There are cases in which it helps type inference.


# Simple Examples

Let's start with some basic examples:
the usual `blah -> Int` stuff:

### List Sum

Let's sum a list:

```scala
val listSum: Algebra[IntListF, Int] = {
  case IntListF.Cons(h, t) => h + t
  case IntListF.Nil        => 0
}
```

How does it work?

```scala
val listSumVerbose: IntListF[Int] => Int = {
  case IntListF.Cons(h, t) => h + t
  //                 |  |
  // Int by definition  |
  //                    Sum of tail (Int)
  case IntListF.Nil => 0
}
```

Notice this is an algebra, to actually use it in you need to call `cata`:

```scala
def sumThisListPlease(list: IntList): Int =
  cata(listSum)(list)
```

For reasons that will become obvious later, when using this stuff in your own
project or libraries, the algebra itself is the unit that you'll be exposing most
often. Instead of creating functions that take fixed-point data (or codata)
structures and return a result, you create algebras and leave it to
users to call `cata` themselves. More on this later but the point is, from the
next example onwards, it'll just be algebras.

### List Length

Counting elements in a list is similar:

```scala
val listLength: Algebra[IntListF, Int] = {
  case IntListF.Cons(_, t) => 1 + t
  case IntListF.Nil        => 0
}
```

How does it work?

```scala
val listLengthVerbose: IntListF[Int] => Int = {
  case IntListF.Cons(_, t) => 1 + t
  //                    |     |
  //                    |     Add 1 for this element
  // Length of tail (Int)
  case IntListF.Nil => 0
}
```

### BinaryTree Algebras

Here's a few algebras for `BinaryTree`:

```scala
val binaryTreeNodeCount: Algebra[BinaryTreeF[Any, ?], Int] = {
  case BinaryTreeF.Node(left, _, right) => left + 1 + right
  case BinaryTreeF.Leaf                 => 0
}

val binaryTreeMaxDepth: Algebra[BinaryTreeF[Any, ?], Int] = {
  case BinaryTreeF.Node(left, _, right) => left.max(right) + 1
  case BinaryTreeF.Leaf                 => 0
}

def binaryTreeSum[N](implicit N: Numeric[N]): Algebra[BinaryTreeF[N, ?], N] = {
  case BinaryTreeF.Node(left, n, right) => N.plus(left, N.plus(n, right))
  case BinaryTreeF.Leaf                 => N.zero
}
```

Pretty straight-forward. Each recursive slot (`left` & `right`) already has the
computed value for that subtree.

### JSON

Let's take a JSON value in our JSON ADT, and turn it into a String that we can
send out the door.

```scala
val jsonToString: Algebra[JsonF, String] = {
  case JsonF.Null        => "null"
  case JsonF.Bool(b)     => b.toString
  case JsonF.Num(n)      => n.toString
  case JsonF.Str(s)      => escapeString(s)
  case JsonF.Arr(values) => values.mkString("[", ",", "]")
  case JsonF.Obj(fields) => fields.iterator.map { case (k, v) => k + ":" + v }.mkString("{", ",", "}")
}
```

Is that easy or what? The array values and object fields are already all Strings,
we just mindlessly combine them using array/object notation.

What if, instead of the slower String concatenation, we wanted to use
`StringBuilder`? Don't let the mutability discourage you; it's the same concept,
we'll just replace `String` in the algebra type signature with
`StringBuilder => Unit`. *Executing* a `StringBuilder => Unit` is mutable but
the function itself is immutable, referentially transparent and pure.
Descriptions of side-effects are safe.

```scala
val jsonToStringSB: Algebra[JsonF, StringBuilder => Unit] = {
  case JsonF.Null        => _ append "null"
  case JsonF.Bool(b)     => _ append b.toString
  case JsonF.Num(n)      => _ append n.toString
  case JsonF.Str(s)      => _ append escapeString(s)
  case JsonF.Arr(values) => sb => {
    sb append '['
    for (v <- values) v(sb)
    sb append ']'
  }
  case JsonF.Obj(fields) => sb => {
    sb append '{'
    for ((k, v) <- fields) {
      sb append k
      sb append ':'
      v(sb)
    }
    sb append '}'
  }
}
```

To be clear, usage would look like this:

```scala
def jsonToStringBuilderUsage(json: Json): String = {
  val sbToUnit = cata(jsonToStringSB)(json)
  val sb = new StringBuilder
  sbToUnit(sb)
  sb.toString()
}
```

# A File System

Let's look at a more interesting example: a file system.

We'll start off with a typical representation with hard-coded recursion.

```scala
sealed trait Entry
final case class Dir(files: Map[String, Entry]) extends Entry
final case class File(size: Long) extends Entry
```

This is an example inhabitant.

```scala
// Example of 3 files:
// 1. /usr/bin/find
// 2. /usr/bin/ls
// 3. /tmp/example.tmp
val example =
  Dir(Map(
    "usr" -> Dir(Map(
      "bin" -> Dir(Map(
        "find" -> File(197360),
        "ls" -> File(133688))))),
    "tmp" -> Dir(Map(
      "example.tmp" -> File(12)))))
```

Now let's create an API:

```scala
def totalFileSize(e: Entry): Long = e match {
  case File(s) => s
  case Dir(fs) => fs.values.foldLeft(0L)(_ + totalFileSize(_))
}

def countFiles(e: Entry): Int = e match {
  case File(_) => 1
  case Dir(fs) => fs.values.foldLeft(0)(_ + countFiles(_))
}

def countDirs(e: Entry): Int = e match {
  case File(_) => 0
  case Dir(fs) => fs.values.foldLeft(1)(_ + countDirs(_))
}
```

Looks great! SHIP IT!
Ok so now people are using our super-awesome file system and associated API.
One day a user wants to collect a bunch of stats and writes the following code:

```scala
final case class Stats(totalSize: Long, files: Int, dirs: Int)

// Traverses FS 3 times! Grossly inefficient
def stats(e: Entry): Stats =
  Stats(totalFileSize(e), countFiles(e), countDirs(e))
```

The user then complains that their `stats` method takes 3 times as long as other
operations. Now obviously, with the pure definitions given above, the extra time
is going to be negligible but imagine it's a real file system here, maybe even one
distributed over the network, all that drive/network/hardware cost to traverse
the file system is likely to be very noticable and very significant when it's
repeated 3 times.

What can the user do? Well... nothing. The only recourse they have is to raise an
issue and complain. They have no control or power in this situation.
They're at the mercy of the decisions made by the library authors.

After a few years of complaints, the authors of the super-awesome file system
library create a new version of their API,
and it looks a little something like this...

```scala
final case class Stats(totalSize: Long, files: Int, dirs: Int)

def stats(e: Entry): Stats = e match {
  case File(fileSize) =>
    Stats(fileSize, 1, 0)
  case Dir(fs) =>
    fs.values.foldLeft(Stats(0, 0, 0)) { (statsAcc, entry) =>
      val b = stats(entry)
      Stats(
        statsAcc.totalSize + b.totalSize,
        statsAcc.files + b.files,
        statsAcc.dirs + b.dirs)
    }
}

def totalFileSize(e: Entry): Long =
  stats(e).totalSize

def countFiles(e: Entry): Int =
  stats(e).files

def countDirs(e: Entry): Int =
  stats(e).dirs
```

KICK-ASS!
Now all stats are gathered in a single traversal; issue: resolved.
Except there are two problems now where there once was one.
First, over the next few versions of the library more and more stats
(permissions, ownership, etc.) get added, and the `stats` function gets bigger,
more complex and more wild.
Second, now new complaints start coming in, complaints like
*"totalFileSize() significantly slower since new update"*,
*"dirCount() 4x slower than in v1.8.3"*. What's going on?
Well, now in every traversal we're spending more time fetching more data that
we don't need and end up throwing away. If a user only wants a directory count,
the library spends oodles of time looking up attributes, group IDs, etc. only
to discard them all at the end.

What can the user do? Well... nothing. The only recourse they have is to raise an
issue and complain. They have no control or power in this situation.
They're at the mercy of the decisions made by the library authors.

### Fixing our FileSystem

Start with the usual changes: type param, `Functor`, `Fix`:

```scala
sealed trait EntryF[+F]
final case class Dir[F](files: Map[String, F]) extends EntryF[F]
final case class File(size: Long) extends EntryF[Nothing]

object EntryF {
  implicit val functor: Functor[EntryF] = new Functor[EntryF] {
    override def map[A, B](fa: EntryF[A])(f: A => B): EntryF[B] = fa match {
      case f: File => f
      case Dir(fs) => Dir(fs.map { case (k, v) => (k, f(v)) })
    }
  }
}

type Entry = Fix[EntryF]
```

Now let's add a little DSL and re-create our sample value:

```scala
object Entry {
  def apply(f: EntryF[Entry]): Entry = Fix(f)
  def file(s: Long): Entry = apply(File(s))
  def dir(es: (String, Entry)*): Entry = apply(Dir(es.toMap))
}

// Example of 3 files:
// 1. /usr/bin/find
// 2. /usr/bin/ls
// 3. /tmp/example.tmp
val example =
  Entry.dir(
    "usr" -> Entry.dir(
      "bin" -> Entry.dir(
        "find" -> Entry.file(197360),
        "ls" -> Entry.file(133688))),
    "tmp" -> Entry.dir(
      "example.tmp" -> Entry.file(12)))
```

Next up are the query logic.
Small, reusable, independent functions are good practice for good reason;
let's recreate what we had in the initial version:

```scala
val totalFileSize: Algebra[EntryF, Long] = {
  case File(s) => s
  case Dir(fs) => fs.values.sum
}

val countFiles: Algebra[EntryF, Int] = {
  case File(_) => 1
  case Dir(fs) => fs.values.sum
}

val countDirs: Algebra[EntryF, Int] = {
  case File(_) => 0
  case Dir(fs) => fs.values.sum + 1
}
```

If you compare this to the first attempt, it's just as simple from the outside,
and even simpler in its internal implementation!

Now what happens when a user wants to get all three stats?
F-Algebras compose. Here's a simple, reusable snippet to combine two F-algebras
that share the same `F`:

```scala
def algebraZip[F[_], A, B](fa: Algebra[F, A],
                           fb: Algebra[F, B])
                          (implicit F: Functor[F]): Algebra[F, (A, B)] =
  fab => {
    val a = fa(fab.map(_._1))
    val b = fb(fab.map(_._2))
    (a, b)
  }
```

This is all the user needs to create their own stats gathering algebra:

```scala
val statsAlg: Algebra[EntryF, (Long, (Int, Int))] =
  algebraZip(totalFileSize, algebraZip(countFiles, countDirs))
```

The `(Long, (Int, Int))` is a little ugly, let's clean it up a bit:

```scala
final case class Stats(totalSize: Long, files: Int, dirs: Int)

def stats(e: Entry): Stats = {
  val (totalSize, (files, dirs)) = cata(statsAlg)(e)
  Stats(totalSize, files, dirs)
}
```

Hoorah. Without any dependencies on the library authors, our user was able to
choose the 3 stats they were interested in, and retrieve them all in a single
file system traversal. Whilst not parallelism, they created their own concurrency!

No contrast this with the previous incarnation.
This time around, the user has the control, the user has the power.
Library authors don't need to decide tradeoffs for everyone.

These are the advantage of providing algebras instead of higher-purpose functions.
F-algebras (like `val statsAlg`) allow you to accrue power;
that power is spent when you apply it (like `def stats`).

In fact, I personally find it nice to provide two interfaces in these scenarios:

1. A low-level ecosystem of algebras, raw data types, logic, etc.
   Usually an entire package.
2. A high-level DSL that very cleanly exposes common high-level functions and
   hide all the algebra composition, calls to `cata` and other morphisms, etc.
   Usually a single `object`.

In this FS example, only `case class Stats` and `def stats(e: Entry): Stats` would
go in the high-level DSL.
This especially makes a nice experience on teams with differing skill levels.
