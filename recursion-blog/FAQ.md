# FAQ

## Why don't you use Matryoshka in your sample code?

There are a few reasons.

1. Recursion scheme theory was invented/discovered outside of any library.
   The knowledge being expressed in this series transcends any implementation.
   What I mean by that is once you learn the concepts, you can go off and apply
   them using Matryoshka or any other library -
   the only difference is syntax (eg. `blah.cata(f)` vs `Recursion.cata(blah)(f)`)
   or maybe some of the basics have different names (`Fix` vs `Mu`, `unfix` vs `embed`),
   and you'll learn that be spending 3 minutes reading the README of the recursion
   library of your choice.

2. Matryoshka is very, very awesome, but shouldn't be considered gospel nor the
   holy grail. Like anything, if has flaws and tradeoffs.
   I'm actually hoping that some of the committers adopt some optimisations I'll
   be demonstrating in this series, and apply them to Matryoshka.

   To be specific,

   * Code is extremely hard to read
     * Implicit ops everywhere - quite hard to find operator definitions
     * Unicode everywhere
     * Super generalised (which is currently a tradeoff, great for flexibility, poor for speed and readability. By specialising more one could have the best of both worlds)
   * Slow and inefficient - some optimisations I'll present achieve over 1000x speedup
   * Semantic flaws - I've discovered one already and will be raising an issue or PR.
     I expect to discover more as I go through this series and increasing my own understanding.

    And because Internet can be so brutally negative:
    Does this mean I {hate, dislike, don't respect, recommend avoiding, whatever}
    Matryoshka? No. I've simply made some observations from my own perspective.
    Matryoshka has a lot of awesome, and I hope that my series inspires some
    improvements to make it even more awesome.
    Shitting on me for observing Matryoshka, or shitting on Matryoshka because
    of my observations makes you immature and an enemy (or at least obstructor)
    of progress. Please don't. It's frustrating that I even have to write this.

3. I want to demonstrate the definitions (implementations) of concepts when I
   introduce them. When the definition are specialised and dependency-free,
   it's really easy to show them in one or two lines.
   This makes it much easier to understand, and IMO a very beneficial learning device.

4. Following on from above, it also makes an important point:
   it's not infeasible or crazy to just copypaste (!) what you need.
   The definitions never change, they're very concise;
   if you're in an environment hostile to adding new dependencies
   you can still use recursion schemes by just copying a few lines of code.
   Literally only a few.
   `Fix` + `cata` + `ana` + `hylo` (which is boundary of what many people understand and use)
    is only 7 lines! If you want optimised versions, it's an extra 6 lines of
    private boilerplate. That's an insanely low one-time cost to a project.


## Which library should I use?

Here are the libraries I know of:

Attributes <-- combine pros & cons, let readers decide whether a point is -/+

Matryoshka
desc
pros
cons

@japgolly's recursion microlib
* Fix is "zero-cost" (i.e. has no memory overhead or allocation)
* Operations are optimised to be around twice as fast/efficient
* Operations specialised and so are faster than their generalised brethren
desc
pros
cons

emilyphi's Cata-Mu-XXX
desc
pros
cons
