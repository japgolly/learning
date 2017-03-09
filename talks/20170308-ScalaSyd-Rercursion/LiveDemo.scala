package demo

import japgolly.microlibs.recursion._
import nyaya.gen._
import play.api.libs.json._

object LiveDemo {

  sealed trait JsonF[+A]
  object JsonF {
    case object Null                              extends JsonF[Nothing]
    case class  Bool(value: Boolean)              extends JsonF[Nothing]
    case class  Str(value: String)                extends JsonF[Nothing]
    case class  Num(value: Double)                extends JsonF[Nothing]
    case class  Arr[A](values: List[A])           extends JsonF[A]
    case class  Obj[A](fields: List[(String, A)]) extends JsonF[A]

    import scalaz._, Scalaz._
    implicit val traverse: Traverse[JsonF] = new Traverse[JsonF] {
      override def traverseImpl[G[_], A, B](fa: JsonF[A])(f: A => G[B])(implicit G: Applicative[G]): G[JsonF[B]] =
        fa match {
          case x@ Null     => G.pure(x)
          case x@ Bool(_)  => G.pure(x)
          case x@ Str(_)   => G.pure(x)
          case x@ Num(_)   => G.pure(x)
          case Arr(values) => values.traverse(f).map(Arr(_))
          case Obj(fields) => fields.traverse { case (k, v) => f(v).map((k, _)) }.map(Obj(_))
        }
    }
  }

  def main(args: Array[String]): Unit = {
    println()
    generateExactDepth(2).samples().take(20).map(_ + "\n").foreach(println)
    println()
  }

  case class Spec(currentDepth: Int, minDepth: Int, maxDepth: Int)  {
    def minDepthReached = currentDepth >= minDepth
    def maxDepthReached = currentDepth >= maxDepth
  }

  val genString = Gen.alphaNumeric.string(0 to 10)

  val generateJson: CoalgebraM[Gen, JsonF, Spec] =
    spec => {
      var gens = List.empty[Gen[JsonF[Spec]]]

      // non-recursive cases
      if (spec.minDepthReached) {
        gens ::= Gen pure JsonF.Null
        gens ::= Gen.boolean.map(JsonF.Bool)
        gens ::= genString.map(JsonF.Str)
        gens ::= Gen.double.map(JsonF.Num)
      }

      // recursive cases
      if (!spec.maxDepthReached) {
        val nextLevel = spec.copy(currentDepth = spec.currentDepth + 1)
        val minSize = if (spec.minDepthReached) 0 else 1
        gens ::= Gen.pure(nextLevel).list(minSize to 4).map(JsonF.Arr(_))
        gens ::= genString.map((_, nextLevel)).list(minSize to 4)
          .map(JsonF.Obj(_))
      }

      Gen.chooseGen_!(gens)
    }

  val jsonToPlayJson: Algebra[JsonF, JsValue] = {
    case JsonF.Null        => JsNull
    case JsonF.Bool(value) => JsBoolean(value)
    case JsonF.Str(value)  => JsString(value)
    case JsonF.Num(value)  => JsNumber(value)
    case JsonF.Arr(values) => JsArray(values)
    case JsonF.Obj(fields) => JsObject(fields)
  }

  def generateExactDepth(depth: Int): Gen[JsValue] =
    generate(depth, depth)

  def generate(minDepth: Int, maxDepth: Int): Gen[JsValue] =
    EasyRecursion.monadicUnfoldIntoFold(
      generateJson, jsonToPlayJson.toAlgebraM[Gen]
    )(Spec(1, minDepth, maxDepth))
}
