package learning.sk_calculus

import scala.annotation.tailrec

object Typed {

  abstract class TermTree[A]  {
    final def apply[T, U](a: TermTree[T])(implicit ev: TermTree[A] =:= TermTree[T => U]): TermTree[U] =
      reduce(Ap(this, a))
  }

  abstract class Term[A] extends TermTree[A]
  case class S[T, U, V]() extends Term[(T => U => V) => (T => U) => T => V]
  case class K[T, U]() extends Term[T => U => T]

  case class I[T]() extends Term[T => T]

  case class Ap[A, B](f: TermTree[A => B], a: TermTree[A]) extends TermTree[B] {
    override def toString = s"$f($a)"
  }

//  @tailrec
  def reduce[A](tt: TermTree[A]): TermTree[A] = tt match {
//    case I() Ap x           => reduce(x)
//    case K Ap x Ap y      => reduce(x)
//    case S Ap x Ap y Ap z => reduce( (x(z))(y(z)) )
    case _                => tt
  }

//  def main(args: Array[String]): Unit = {
//    println()
//
//    def T = K
//    def F = S(K)
//    def and = S(K)
//    def or = K
//
//    def flip = S(K(S(I)))(K)
//
//    //    def fmt(t: TermTree) = t.toString match {
//    //      case "K"    => "T"
//    //      case "S(K)" => "F"
//    //      case s      => s
//    //    }
//
//    def test2(mk: (TermTree, TermTree) => (TermTree, TermTree, TermTree)): Unit = {
//      for {a <- List(T, F); b <- List(T, F)} {
//        val seq = mk(a, b)
//        val r = seq._1(seq._2)(seq._3)
//        println(s"$seq = $r")
//      }
//      println()
//    }
//
//    test2((_, or, _))
//    test2((_, _, and))
//  }

}
