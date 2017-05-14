package learning.sk_calculus

import scala.annotation.tailrec

/** Direct encoding */
object Direct {

  abstract class Term(f: Term => Term) {
    final def apply(t: Term): Term = f(t)
  }

  case class λ(f: Term => Term) extends Term(f)

  /** Identity */
  case object I extends Term(x => x)

  /** Const */
  case object K extends Term(x => λ(y => x))

  /** Substitution */
  case object S extends Term(x => λ(y => λ(z => (x(z)) (y(z)))))

  val DerivedI = S(K(null))
}

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

///** Sequential encoding */
//object Sequential {
//
//  abstract class Term
//  case object S extends Term
//  case object K extends Term
//  case object I extends Term
//
//  type Terms = List[Term]
//  def Terms(terms: Term*): Terms = terms.toList
//
//  @tailrec
//  def reduce(terms: Terms): Terms = terms match {
//    case Nil                   => Nil
//    case I :: x           :: t => reduce(x :: t)
//    case K :: x :: y      :: t => reduce(x :: t)
//    case S :: x :: y :: z :: t => oops, is tree stupid!
//    case _                     => terms
//  }
//}

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/** Tree encoding */
object Tree {

  abstract class TermTree {
    final def apply(a: TermTree): TermTree =
      reduce(Ap(this, a))
  }

  abstract class Term extends TermTree
  case object S extends Term
  case object K extends Term
  case object I extends Term

  case class Ap(f: TermTree, a: TermTree) extends TermTree {
    override def toString = s"$f($a)"
  }

  @tailrec
  def reduce(tt: TermTree): TermTree = tt match {
    case I Ap x           => reduce(x)
    case K Ap x Ap y      => reduce(x)
    case S Ap x Ap y Ap z => reduce( (x(z))(y(z)) )
    case _                => tt
  }

  def main(args: Array[String]): Unit = {
    println()

    def T = K
    def F = S(K)
    def and = S(K)
    def or = K

    def flip = S(K(S(I)))(K)

//    def fmt(t: TermTree) = t.toString match {
//      case "K"    => "T"
//      case "S(K)" => "F"
//      case s      => s
//    }

    def test2(mk: (TermTree, TermTree) => (TermTree, TermTree, TermTree)): Unit = {
      for {a <- List(T, F); b <- List(T, F)} {
        val seq = mk(a, b)
        val r = seq._1(seq._2)(seq._3)
        println(s"$seq = $r")
      }
      println()
    }

    test2((_, or, _))
    test2((_, _, and))
  }

}
