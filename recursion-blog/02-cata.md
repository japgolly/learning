Recursion schemes are awesome, and practical.
This is chapter 2 in a [series of blog posts about recursion schemes](https://github.com/japgolly/learning/tree/public/recursion-blog).
This series uses Scala, and will focus on usage and applicability.
It will be scarce in theory, and abundant in examples.
The theory is valuable and fascinating, but I often find that knowing the theory alone is only half understanding.
The other half of understanding comes from, and enables, practical application.
I recommend you bounce back and forth between this series and theory.
The internet is rich with blogs and videos on theory that explain it better than I would, so use those awesome resources.

## Before you start...

If you don't know what I mean by `Fix[_]`,
read [chapter 1 of this series](https://japgolly.blogspot.com/2017/11/practical-awesome-recursion-ch-01.html).

This series doesn't depend on, or emphasise, Matryoshka or any other library.
If you'd like to understand why, I've explained [here in the FAQ](TOOODOOOO).

## The Catamorphism

What is a catamorphism?
It can be answered from a few perspectives.

### What

It's often referred to as a fold over your data structure.
Examples that sum or count values are very common.
eg. `List(1, 3, 7).foldLeft(0)(_ + _) == 11`.
As you'll see below, folds are catamorphisms are capable of much more than calculating numbers.

It's defined as:

```scala
def cata[F[_] : Functor, A, B](fAlgebra: F[A] => A)(f: Fix[F]): A =
  fAlgebra(f.unfix.map(cata(fAlgebra)))
```

The first argument `fAlgebra` is so called because `F[A] => A` is known as an
F-algebra. *What* it is, is your folding-logic function that inspects a single
level/layer of your structure without recursion.
The `f: Fix[F]` is the data structure that you want to fold into some type `A`.
Combine the two with this magic function and all the recursion is taken care of
for you, and the result is just a single `A`. If you're confused, the examples
below will clear it up.

Level? Layer? Visualise your recursive data types like this:
```
IntListF (1 to 5)
=================

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
It's an interesting note about parametricity. The only means it
has of producing an `A` is to call `fAlgebra`... which requires an `F[A]`...
so how do you put an `A` in the `F[_]` if you can't produce `A`s?
Remember that the hole if `F[_]` represents the recursive case?
In non-recursive cases (eg. `Nil` in a cons list) the type is a phantom-type,
covariant and always `Nothing`, or completely unused. For example:

```scala
case class Eg[A](int: Int)

def changeIt[X, A](eg: Eg[X]): Eg[A] =
  Eg(eg.int)
```

See? When a type variable is unused you can replace it with anything you want,
which is exactly what happens in `Functor[F]`.

It's also important to understand the order in which things happen.
Catamorphisms:

1. start at the root (their input, the `f: Fix[F]`)
2. (computationally) move to the leaves
3. calculate their way back to the root

Which means your folding logic is going to start executing against all the leaves
first, then their parents, then *their* parents, etc.
When we get to some of the more advanced morphisms, understanding the order becomes critical.


### Optimisation

I did say that this is a practical series.
This is a good a place as any to mention that this definition, while correct,
is inefficient.

Every time it recurses it has to create the same functions with the same logic
over and over again.

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
110%? 120%?

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
even at structure size of 1x10000 (length x depth). It'd be interesting to know
what the measurements would be in prod, on real GCP/AWS VMs.
They'd be slower for sure (i.e. the savings would be more significant.)*
