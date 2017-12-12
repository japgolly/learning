package japgolly.blog.recursion.shared

import japgolly.microlibs.recursion.Fix
import scalaz.Functor

sealed trait IntListF[+F]

object IntListF {
  final case class Cons[+F](head: Int, tail: F) extends IntListF[F]
  case object Nil extends IntListF[Nothing]

  implicit val functor: Functor[IntListF] = new Functor[IntListF] {
    override def map[A, B](fa: IntListF[A])(f: A => B): IntListF[B] = fa match {
      case Cons(head, tail) => Cons(head, f(tail))
      case Nil              => Nil
    }
  }

  object IntList {

    // Helpful cos Scala's type inference fails so often
    def apply(f: IntListF[IntList]): IntList =
      Fix(f)

    def nil: IntList =
      apply(Nil)

    def cons(head: Int, tail: IntList): IntList  =
      apply(Cons(head, tail))

    def fromList(is: Int*): IntList  =
      is.foldRight(nil)(cons)
  }

}
