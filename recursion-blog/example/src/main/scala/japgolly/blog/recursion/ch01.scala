package japgolly.blog.recursion.ch01

import japgolly.blog.recursion.definitions.Fix
import scalaz.Functor

object IntListExample {

  object Before {
    sealed trait IntList
    final case class IntCons(head: Int, tail: IntList) extends IntList
    case object IntNil extends IntList
  }

  object After {
    sealed trait IntListF[+F]
    final case class IntCons[+F](head: Int, tail: F) extends IntListF[F]
    case object IntNil extends IntListF[Nothing]

    implicit val functor: Functor[IntListF] = new Functor[IntListF] {
      override def map[A, B](fa: IntListF[A])(f: A => B): IntListF[B] = fa match {
        case IntCons(head, tail) => IntCons(head, f(tail))
        case IntNil              => IntNil
      }
    }

    type IntList = Fix[IntListF]

    object IntList {
      // Helpful cos Scala's type inference fails so often
      def apply(f: IntListF[IntList]): IntList =
        Fix(f)

      def nil: IntList =
        apply(IntNil)

      def cons(head: Int, tail: IntList): IntList  =
        apply(IntCons(head, tail))

      def fromList(is: Int*): IntList  =
        is.foldRight(nil)(cons)
    }
  }

}

// █████████████████████████████████████████████████████████████████████████████████████████████████████████████████████

object BinaryTreeExample {

  object Before {
    sealed trait BinaryTree[+A]
    final case class Node[+A](left: BinaryTree[A], value: A, right: BinaryTree[A]) extends BinaryTree[A]
    case object Leaf extends BinaryTree[Nothing]
  }

  object After {
    sealed trait BinaryTreeF[+A, +F]
    final case class Node[+A, +F](left: F, value: A, right: F) extends BinaryTreeF[A, F]
    case object Leaf extends BinaryTreeF[Nothing, Nothing]

    implicit def functor[A]: Functor[BinaryTreeF[A, ?]] = new Functor[BinaryTreeF[A, ?]] {
      override def map[B, C](fa: BinaryTreeF[A, B])(f: B => C): BinaryTreeF[A, C] = fa match {
        case Node(left, value, right) => Node(f(left), value, f(right))
        case Leaf                     => Leaf
      }
    }

    type BinaryTree[A] = Fix[BinaryTreeF[A, ?]]
  }

}

// █████████████████████████████████████████████████████████████████████████████████████████████████████████████████████


object JsonExample {

  object Before {
    sealed trait Json
    object Json {
      case object      Null                               extends Json
      final case class Bool(value: Boolean)               extends Json
      final case class Str (value: String)                extends Json
      final case class Num (value: Double)                extends Json
      final case class Arr (values: List[Json])           extends Json
      final case class Obj (fields: List[(String, Json)]) extends Json
    }
  }

  object After {
    sealed trait JsonF[+F]
    object JsonF {
      case object      Null                              extends JsonF[Nothing]
      final case class Bool  (value: Boolean)            extends JsonF[Nothing]
      final case class Str   (value: String)             extends JsonF[Nothing]
      final case class Num   (value: Double)             extends JsonF[Nothing]
      final case class Arr[F](values: List[F])           extends JsonF[F]
      final case class Obj[F](fields: List[(String, F)]) extends JsonF[F]

      implicit val functor: Functor[JsonF] = new Functor[JsonF] {
        override def map[A, B](fa: JsonF[A])(f: A => B): JsonF[B] = fa match {
          case Null        => Null
          case j: Bool     => j
          case j: Str      => j
          case j: Num      => j
          case Arr(values) => Arr(values.map(f))
          case Obj(fields) => Obj(fields.map { case (k, v) => (k, f(v)) })
        }
      }

      type Json = Fix[JsonF]
    }
  }

}
