# 4

Terms can be represented as values or functions.

## 4.1 Term representation

* Create a restricted subset of terms ("simplified forms") that, when considering algebraic laws, can still represent all terms.

* When choosing a simplified form, don't worry whether all terms can be put into it -- just try to derive terminating definitions for the operations, and if we succeed, the result follows.

## 4.2 Context-Passing representation

* Observation = operation from algebra out to some external representation. eg. MyList A => List A

* Representation as functions from their context to the observation being made. This allows operations to behave differently than their syntax/structure (eg.  associative syntax but want to avoid (quadratic) left binds, allow the operation to right bind (linear) by looking at its parent context.)

* Model
  * Context has a hole in which the child is inserted: `C(_)`.
  * Operations/cases that don't care about context can just ignore it.
  * `C[*] ::= list [*] | list ([*] ++ MyList)`
  * `data Ctx a = List | ListCat (MyList a)`
  * `type MyList a = Ctx a -> [a]`

## 4.3

* Look at the operation functions and see if any arguments have more info than needed. If so, simplify in the model.

Which leads to a simplification from
  * `data Ctx a = List | ListCat (MyList a)`
  * `type MyList a = Ctx a -> [a]`
to
  * `type Ctx a = [a]`
  * `type MyList a = Ctx a -> [a]`


# 7. Specifying Pretty-Printing

Design:
1. Model & Combinators
2. Algebraic properties
3. Derive implementations (using techniques like in ↑4↑)

## 7.1

Model output. (i.e pretty-printed text).
`String` is too useless.
Maybe list of line and their indent levels. `NonEmptyVector[(Int, String)]`

## 7.2

Formal laws/properties helped because:
* reduced the number of things lib users need to think about (specially due to associativity) = less cognative burden = less subtle "bugs" (i.e. representations that don't match user's intent)
* for the lib author, each law simplifies optimisation.
* reveal subtle errors

## 7.3

Model all possibilities and a method for selecting the best.
* `type Doc = Set Layout`
* `best :: Doc -> Layout`

Now all `Layout` ops can be promoted to Doc ops.

Because all laws are linear (i.e. no variable appears more than once on either side of `=`), the same laws all hold for `Doc` too.

## 7.4

Create an Ordering to order all lines.

* `nice line :: Boolean` - some lines can't be made pretty (eg. a string of 999 chars)
* `line > line :: Boolean` - an ordering using `nice` and line lengths
* Extend line comparison to layout comparison by using lexicographic ordering (i.e. the same way `Ordering[String]` can be derived from `Ordering[Char]`)
* Lexicographic ordering can also be written as `(A,A)->A` like min/max which makes it easy to apply to an unordered stream.
* `best :: Doc -> Layout` just orders layouts by above and takes head.


# 8. Implementation

Using the representations above are too naive; docs as a list of alternate layouts could quickly result in billions and bilions of elements.

* Create an algebra that matches the `best` function's laws and easy to write
* Then simplify (rewrite) it, to make sure that the line ordering function is similarly easy to write
