package japgolly.blog.recursion.shared

import japgolly.microlibs.recursion._
import scalaz.{Applicative, Traverse}

sealed trait CalculatorF[+F]
object CalculatorF {
  final case class Literal(value: Double) extends CalculatorF[Nothing]
  final case class Add     [+F](l: F, r: F) extends CalculatorF[F]
  final case class Subtract[+F](l: F, r: F) extends CalculatorF[F]
  final case class Multiply[+F](l: F, r: F) extends CalculatorF[F]
  final case class Divide  [+F](l: F, r: F) extends CalculatorF[F]

  implicit val traverse: Traverse[CalculatorF] = new Traverse[CalculatorF] {

    override def map[A, B](fa: CalculatorF[A])(f: A => B): CalculatorF[B] = fa match {
      case l: Literal     => l
      case Add     (l, r) => Add     (f(l), f(r))
      case Subtract(l, r) => Subtract(f(l), f(r))
      case Multiply(l, r) => Multiply(f(l), f(r))
      case Divide  (l, r) => Divide  (f(l), f(r))
    }

    override def traverseImpl[G[_], A, B](fa: CalculatorF[A])(f: A => G[B])(implicit G: Applicative[G]) = fa match {
      case l: Literal     => G point l
      case Add     (l, r) => G.apply2(f(l), f(r))(Add     (_, _))
      case Subtract(l, r) => G.apply2(f(l), f(r))(Subtract(_, _))
      case Multiply(l, r) => G.apply2(f(l), f(r))(Multiply(_, _))
      case Divide  (l, r) => G.apply2(f(l), f(r))(Divide  (_, _))
    }
  }

  val plusOnes: Coalgebra[CalculatorF, Int] =
    i => if (i < 2) Literal(i) else Add(1, i - 1)

  val evalBasic: Algebra[CalculatorF, Double] = {
    case Literal(i)     => i
    case Add     (a, b) => a + b
    case Subtract(a, b) => a - b
    case Multiply(a, b) => a * b
    case Divide  (a, b) => a / b
  }

  object Calculator {
    def apply(f: CalculatorF[Calculator]): Calculator =
      Fix(f)
  }
}