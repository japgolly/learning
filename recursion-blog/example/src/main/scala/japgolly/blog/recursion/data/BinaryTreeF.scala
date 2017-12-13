package japgolly.blog.recursion.data

import scalaz.Functor

sealed trait BinaryTreeF[+A, +F]
object BinaryTreeF {

  final case class Node[+A, +F](left: F, value: A, right: F) extends BinaryTreeF[A, F]
  case object Leaf extends BinaryTreeF[Nothing, Nothing]

  implicit def functor[A]: Functor[BinaryTreeF[A, ?]] = new Functor[BinaryTreeF[A, ?]] {
    override def map[B, C](fa: BinaryTreeF[A, B])(f: B => C): BinaryTreeF[A, C] = fa match {
      case Node(left, value, right) => Node(f(left), value, f(right))
      case Leaf                     => Leaf
    }
  }
}
