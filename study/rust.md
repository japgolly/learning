Rust tools
==========

Install rustup
rustup default stable
rustup component add rust-src # (for auto-completion)
cargo install racer # (for auto-completion)
cargo install rustfmt

Rust language
=============

#### vs Scala

use a::b                  = import a.b
use a::b::*               = import a.b._
let                       = val
let mut                   = var
match a { b => c }        = a match { case b => c }
fn a(b: C) -> D {…}       = def a(b: C): D = {…}
if c {a} else {b}         = if (c) a else b
while c {a}               = while (c) a
for a in b {c}            = b.foreach(a => a⊢c)
m..n                      = m to n
struct X {a:A, b:B}       ≈ case class X(a: A, b: B)
X {a:f, b:g}              = X(a = f, b = g)
X {a:f, ..y}              = y.copy(a = f)
if let a = b {c}          = b match { case a => c; case _ => () }
if let a = b {c} else {d} = b match { case a => c; case _ => d }
|a| b                     = (a => b)
|a: B| -> C {d}           = (a => d): B => C
type A = B                = type A = B
const A: B = C            = @inline/final val A: B = C
a as B                    = a: B
trait A { type B }        = same
trait A { type B: C }     ≈ trait A { type B; implicit val _: C[B] }


#### vs Haskell

trait A<B>             = class A B where
impl A for B           = instance A B where
enum A {B,C(D),E{f:G}} = data A = B | C D | E { f :: G }
struct X(A, B)         ≈ newtype X = (A,B)

#### Desc

&x                  = immutable reference
&mut x              = mutable reference
loop {…}            = while(true) {…} - supports `break;` & `continue;`
&x[a..b]            = Substring of chars [a,b) of string x. a and b can be omitted.
&str                = Type of string literals. Also inhabited by `&String`.
String              = Heap-allocated, mutable string.

#### Notes

* You can shadow local variables
* Integers: {i,u}{8,16,32,64,size} where size = arch size (eg. 64 on x64)
* Floating: f{32,64}
* Boolean = `bool` = `true`|`false`
* Char = `char` of range [0,D7FF]+[E000,10FFFF]
* Literals: Int: `123i64`, byte: `b'A'` (`u8` only), underscores ok: `123_456`
* Tuples: type like Scala, can destructure on `let`, accessors are `.0`, `.1` etc
* Arrays: `[1,2,3]`, `a[0]` access, stack-allocated
* Ops via impl:
    ```
    impl Rectangle {

        // "Associated function"
        // USAGE: Rectangle::square(4): Rectangle
        fn square(size: u32) -> Rectangle {
            Rectangle { length: size, width: size }
        }

        // "Method"
        // USAGE: rect.area(): u32
        fn area(&self) -> u32 {
            self.length * self.width
        }
    }
    ```
* Ownership & malloc
  * move = shallow copy and invalidation
  * Drop trait = deconstructor
  * Copy trait = ownership never transfered (never moved), instead data copied. stack-only ∴ Drop-disjoint
  * Tuples that derive Copy are created on stack.
  * Copy/move on `let`, pass to fn, fn return
  * References borrow ownership; ownership is returned implicitly when borrow ends
  * Multiple immutable references allowed; only 1 mutable reference allowed per scope.
  * `'x` is a phantom-type that captures a lifetime.
    eg. `fn longest<'a>(x: &'a str, y: &'a str) -> &'a str`
  * Closures represented as Fn(A) -> B ≈ A => B. Wrt captured data:
    * `Fn` = borrow from env immutably. `|a| a == b`
    * `FnMut` = borrow from env mutably.
    * `FnOnce` = take ownership. Can only be invoked once. `move |a| a == b`
* Underscores in a type instruct Rust to infer, eg `HashMap<_, _>`
* Appending a `?` to a `Result` is like `if r.is_err() {return r} else {r.get()}`
  (Hardcoded sugar for disjuction monad.)
* Generics
  * Append `<A,B,…>` to data type names, `impl` keyword, fn names
  * ∃ Compiler phase, monomorphization (= specialization)
  * Types can have context bounds like in Scala (eg. `A: Equal`)
  * Multiple trait bounds compose with `+` (eg. `A: Equal + Hash`)
  * Trait bounds can be moved to after return type with `where`
    Eg. `fn eq<A>(a: A, b: A) -> bool where A: Equal`
* Variables starting with `_` do not omit warnings when unused
* `#[a] b` = `b { #![a] }`

Rust stdlib
===========

Result A E = Ok A | Err E
  `and`       = `>>`
  `and_then`  = `>>=`
  `unwrap_or` = `getOrElse`
  `unwrap`    = `get`
