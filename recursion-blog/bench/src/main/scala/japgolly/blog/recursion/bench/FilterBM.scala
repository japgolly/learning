/*package japgolly.blog.recursion.bench

import java.util.concurrent.TimeUnit
import japgolly.blog.recursion.data._
import japgolly.microlibs.recursion._
import org.openjdk.jmh.annotations._
import scalaz.Functor
import scalaz.syntax.functor._

object FilterBM {

  def strict(cutoff: Int): Algebra[IntListF, IntList] = {
    case c@ IntListF.Cons(h, _) if h <= cutoff => IntList(c)
    case _ => IntList.nil
  }

  def fn0(cutoff: Int): Algebra[IntListF, () => IntList] = {
    case IntListF.Cons(h, t) if h <= cutoff => () => IntList.cons(h, t())
    case _ => () => IntList.nil
  }

}

@Warmup(iterations = 20)
@Measurement(iterations = 20)
@Fork(2)
@BenchmarkMode(Array(Mode.AverageTime))
@OutputTimeUnit(TimeUnit.MICROSECONDS)
@State(Scope.Benchmark)
class FilterBM {

  @Param(Array("20000"))
  var size: Int = _

  @Param(Array("0", "10000", "20000"))
  var cutoff: Int = _

  var i: IntList = _

  @Setup def setup = {
    i = IntList.fromList(0 to size: _*)

//    val listLength: Algebra[IntListF, Int] = {
//      case IntListF.Cons(_, t) => 1 + t
//      case IntListF.Nil        => 0
//    }
//    val x = Recursion.cata(FilterBM.strict(cutoff))(i)
//    val y = Recursion.cata(listLength)(x)
//
//    println(s"cutoff = $cutoff, result size = $y")
  }

  @Benchmark def filter: IntList = Recursion.cata(FilterBM.strict(cutoff))(i)
  @Benchmark def filter2: IntList = Recursion.cata(FilterBM.fn0(cutoff))(i).apply()
}
*/