package japgolly.blog.recursion.shared

import japgolly.microlibs.recursion.Fix
import scalaz.Functor

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

  object Json {
    def apply(f: JsonF[Json]): Json =
      Fix(f)
  }
}
