"Recursion schemes are Awesome! They're practical too."
PARS

"The point of this series is *not* for you to write your own recursion scheme library."
Points of this series:
*
Not the point of this series:
* you write your own recursion scheme library


What's the point?
=================
* Intuitions above morphisms
* How they work
* Examples: simple (list,trees,dsl,nat,json)
* Examples: real-world (like Coins)

What's out of scope?
====================
* Impl details of morphisms

Questions for myself
====================
Can I avoid AtomOrComposite?


cata
====

OUTLINE
=======

- Prereqs
  - Read prev first
- Cata
  - Address library choice
  - Definition
  - Optimisation
  - Explanation & Intuition (fold but way more, let's start with fold though)
- Typical/Boring stuff (F -> Int)
  - IntList sum & count
  - BinaryTree node count, maxDepth
- JSON is very common
  - JSON string (F -> String) - so easy
- Scenario: FileSystem
  - create simple functions
  - Sequential. Inefficient - you have no power!
  - inverse
  - inefficient - you still have no power!
  - Use fix and simple algebras, zip for parallelism. You have the power!
  - show low/high -level organisation (high = dsl object)
- cata is also your map & filter
  - map
  - filter - discuss inefficiency of strict semantics
- cata is also your trans
  - FS to JSON
- Monadic version
  - calculator eval - how to handle division by 0
  - Definition
  - Optimisation
  - Functor -> Traverse
  - calculator to String \/ Double
- Stack-safe?
  - use the monadic version

- Summary
  - cata is your fold/map/filter/trans
  - cata starts at the root, moves to leaves (1), and calculates its way back to the root (2)
  - cata operations can be composed to run in a single pass
  - cata can run in another effect

- Other
F-algebra (FA -> A) = copoint on comonads. Any good examples?
Or, any other interesting examples that show a perspective distinct from what I've shown above?
Contact me at ___ and I'll include it in a follow-up post.



- address "why aren't you using Matryoshka?"
- add a list of libraries to public/README.md

my goal is to show different ways/application.
fold isn't just for sum and max etc

- fold doesn't always need to be a single value, can also be another tree
- fold / transform from leaves back to root
- direction is important to know for morphisms

- IntList - sum, count
- BinTree (?) - maybe something to do with how balanced a tree is?
- JSON AST to String (unparse)
- calculator over String \/ (evaluation)
- Should do a Trie! -> List[String] -- Scrabble
- algebra composition - zipping is a good example to compare with two manually recursive fns
- comonad
- file system

- save this for next episode?
- Scenario: Scrabble
  - Problem
  - Trie
  - TrieSet && toList
  - Revisit in ep 3
  - Trie -> Json
  - Compare JSON sizes

ana
===
- IntList - seed value
- primes
- Should do a Trie!
- json generator over Gen
- dsl over State
- search through a BinTree - F -> ? \/ A (link to decision tree video and credit girl)
- parser (ask readers or try myself. Maybe a futu)


hylo
====
"Hylomorphisms, or hylos for short, are solutions to a recursion
scheme that captures the essence of divide-and-conquer algorithms.
Such algorithms have three phases: first, a problem is broken into sub-problems by a coalgebra; second, sub-problems are recursively
and independently turned into sub-solutions; and finally,
sub-solutions are combined by an algebra to form a solution"
