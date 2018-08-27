import scalaz.{Applicative, Traverse}

final case class NonEmptyList[A](head: A, tail: List[A]) {
  def size = 1 + tail.size

  def map[B](f: A => B): NonEmptyList[B] =
    new NonEmptyList(f(head), tail.map(f))

  def toList: List[A] =
    head :: tail

  def toMap[K,V](implicit ev: A <:< (K, V)): Map[K, V] =
    toList.toMap

  def apply(i: Int): A =
    if (i == 0)
      head
    else
      tail(i - 1)
}

object NonEmptyList {
  def apply[A](head: A, tail: A*): NonEmptyList[A] =
    new NonEmptyList(head, tail.toList)

  implicit def traverse: Traverse[NonEmptyList] =
    ??? // exercise to the reader
}

// =====================================================================================================================

sealed trait Json {
  final def stringValue: Json.ParseResult[String] = this match {
    case Json.Str(s) => Right(s)
    case _ => Json.fail("Not a JSON string: " + this)
  }
  final def intValue: Json.ParseResult[Int] = this match {
    case Json.Num(d) => Right(d.toInt)
    case _ => Json.fail("Not a JSON number: " + this)
  }
  final def get(fieldName: String): Json.ParseResult[Json] = this match {
    case Json.Object(fs) => fs.find(_._1 == fieldName) match {
      case Some((_, v)) => Right(v)
      case None => Json.fail(s"Field '$fieldName' not present in $this")
    }
    case _ => Json.fail("Not a JSON object: " + this)
  }
  final def nonEmptyList: Json.ParseResult[NonEmptyList[Json]] =
    ??? // exercise to the reader
}
object Json {
  case class Num(value: Double) extends Json
  case class Str(value: String) extends Json
  case class Array(toList: List[Json]) extends Json
  case class Object(fields: List[(String, Json)]) extends Json

  type ParseResult[+A] = Either[String, A]
  def fail(reason: String) = Left(reason)
}

// =====================================================================================================================

final class IO[A](val unsafePerformIO: () => A) extends AnyVal {
  def map[B](f: A => B): IO[B] = IO(f(unsafePerformIO()))
  def flatMap[B](f: A => IO[B]): IO[B] = IO(f(unsafePerformIO()).unsafePerformIO())
}
object IO {
  def apply[A](a: => A): IO[A] =
    new IO(() => a)

  implicit def applicative: Applicative[IO] =
    ??? // exercise to the reader
}