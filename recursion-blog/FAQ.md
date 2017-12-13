# FAQ

## Why don't you use Matryoshka in your sample code?

A very common question. I'll explain.
There are a few reasons.

1. Recursion scheme theory was invented/discovered outside of any library.
   The knowledge being expressed in this series transcends any implementation.
   What I mean by that is once you learn the concepts, you can go off and apply
   them using Matryoshka or any other library -
   the only difference is syntax (eg. `blah.cata(f)` vs `Recursion.cata(blah)(f)`)
   or maybe some of the basics have different names (`Fix` vs `Mu`, `unfix` vs `embed`),
   and you'll learn that within 3 minutes of reading the README of the recursion
   library of your choice.

2. Matryoshka is very, very awesome, but shouldn't be considered gospel nor the
   holy grail. Like anything, if has flaws and tradeoffs.

   * Code is extremely hard to read
     * Implicit ops everywhere - quite hard to find operator definitions.
       This is huge to me, over the years I've become very opposed to libraries
       adding extension methods to everything.
     * Unicode everywhere
   * Could be more efficient - some optimisations I'll present in the series achieve over 1000x speedup
   * Semantic flaws - I've discovered one already and will be raising an issue or PR.
     I expect to discover more as I go through this series and increasing my own understanding.

    Now don't get me wrong - I like Matryoshka.
    I've simply made some observations and think we're still at a stage where
    considering different implementations is valuable both
    to users/projects with different value criteria, and Matryoshka itself.
    I hope that my series inspires some improvements to make Matryoshka even better.

3. I want to demonstrate the definitions (implementations) of concepts when I
   introduce them. When the definition are specialised and dependency-free,
   it's really easy to show them in one or two lines.
   This makes it much easier to understand, and IMO a very beneficial learning device.

4. Following on from above, it also makes an important point:
   it's not infeasible or crazy to just copypaste (!) what you need.
   The definitions never change, they're very concise;
   if you're in an environment hostile to adding new dependencies or
   dependencies of which your team will only comprehend and use 10%,
   you can still use recursion schemes by just copying a few lines of code.
   Literally only a few.
   `Fix` + `cata` + `ana` + `hylo` (which is boundary of what many people understand and use)
    is only 7 lines! If you want optimised versions, it's an extra 6 lines of
    private boilerplate. That's an insanely low, one-time cost to a project.


## Which library should I use?

Here are the libraries I know of:

* [Matryoshka](https://github.com/slamdata/matryoshka)
  * Very comprehensive, has nearly everything
  * Unoptimised: usually over twice as slow as possible
  * *Lots* of implicit extension methods
  * Very generalised

* [@japgolly's recursion micro-library](https://github.com/japgolly/microlibs-scala)
  * Contains most common stuff but not everything. Still growing but no idea how comprehensive it will become
  * Optimised: fastest and most memory-efficient Scala implementation I've seen
  * Very few implicit extension methods
  * Specialised (for performance), not much generalisation (yet)

* [emilyphi's Cata-Mu-Fix](https://github.com/emilypi/Cata-Mu-Fix)
  * TODO
