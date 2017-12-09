

# More than fold

If you're used to thinking in terms of Scala collections,
catamorphism is more than the `.fold{,Left,Right}` methods, it's also your
`.map` and `.filter`.
If you know what a natural transformation is (`forall A. F[A] => G[A]`),
it can also be one of those.

### Map

Let's say you want to modify all files in a file system value:

```scala
def mapFiles(f: File => File): FAlgebra[EntryF, Entry] = {
  case a: File       => Entry(f(a))
  case a: Dir[Entry] => Entry(a)
}
```

or if that's a bit confusing, this is the same thing:
```scala
def mapFiles(f: File => File): FAlgebra[EntryF, Entry] = {
  case a: File       => Fix[EntryF](f(a))
  case a: Dir[Entry] => Fix[EntryF](a)
}
```

Then we can make more concrete functions like:

```scala
// Demonstrating Entry => Entry here instead of Algebra[EntryF, Entry]
val doubleFileSizes: Entry => Entry = {
  val alg = mapFiles(f => f.copy(size = f.size * 2))
  cata(alg)(_)
}
```

### Filter

Let's say you want to filter your file system by file and directory names.
Easy:

```scala
def filter(f: String => Boolean): FAlgebra[EntryF, Entry] = {
  case a: File => Entry(a)
  case Dir(fs) => Entry(Dir(fs.filterKeys(f)))
}
```

Now there's an interesting point to be made here.
A lot of Scala is ported from Haskell but it's important to remember that Scala
is not Haskell. Haskell is a lazily-evaluated language where as Scala is strict
meaning computation orders and performance profiles differ.
I said earlier that catamorphisms are evaluated from leaves back to the root,
which means there's potential for a bunch of work to be done and then thrown away
when it's branch is later pruned from the final result.

One way to mitigate this, is to regain control of evaluation; instead of returning
a result, return a function to the result. This gives us the ability to decide
when to evaluate the functions, if at all. If we modify our filter algebra
accordingly we get:

```scala
def filter2(f: String => Boolean): FAlgebra[EntryF, () => Entry] = {
  case a: File => () => Entry(a)
  case Dir(fs) => () => Entry(Dir(fs.iterator.filter(x => f(x._1)).map(x => (x._1, x._2())).toMap))
}
```

It's a bit messier but you can see that the `.filter` occurs before the `x._2()`,
the `()` part going off and evaluating the subtree.

Usage is pretty similar, just tack a `.apply()` on the end (when Dotty comes out,
a `()` will be sufficient).

```scala
val exampleWithoutTempFiles: Entry =
  cata(filter2(_ endsWith ".tmp"))(example).apply()
```

I put this to JMH to measure the difference.
Instead of a FS example, I used `IntList` and did the equivalent of
`(0 to 20000).toList.takeWhile(_ <= cutOff)` and here are the results:

```
[info] Benchmark        (cutoff)  (size)  Mode  Cnt    Score    Error  Units
[info] FilterBM.filter         0   20000  avgt   10  250.973 ±  1.506  us/op
[info] FilterBM.filter     10000   20000  avgt   10  261.846 ±  9.410  us/op
[info] FilterBM.filter     20000   20000  avgt   10  250.119 ±  8.496  us/op
[info] FilterBM.filter2        0   20000  avgt   10  224.236 ±  9.256  us/op
[info] FilterBM.filter2    10000   20000  avgt   10  355.324 ± 13.272  us/op
[info] FilterBM.filter2    20000   20000  avgt   10  465.920 ± 19.401  us/op
```

The non-strict version, `filter2`, is
~86% faster when nothing is filtered out,
~40% faster when half the list is filtered out, and
~10% slower when everything is filtered out.
