package japgolly.blog.recursion.bench

import java.util.concurrent.TimeUnit
import japgolly.blog.recursion.shared._
import japgolly.microlibs.recursion._
import org.openjdk.jmh.annotations._
import scalaz.Functor
import scalaz.syntax.functor._

object CataBM {

  def basic[F[_] : Functor, A, B](fAlgebra: F[A] => A)(f: Fix[F]): A =
    fAlgebra(f.unfix.map(basic(fAlgebra)))

  def optimised[F[_], A, B](algebra: F[A] => A)(f: Fix[F])(implicit F: Functor[F]): A = {
    var self: Fix[F] => A = null
    self = f => algebra(F.map(f.unfix)(self))
    self(f)
  }
}

@Warmup(iterations = 4)
@Measurement(iterations = 4)
@Fork(1)
@BenchmarkMode(Array(Mode.AverageTime))
@OutputTimeUnit(TimeUnit.MICROSECONDS)
@State(Scope.Benchmark)
class CataBM {

  @Param(Array("10", "100", "1000", "10000"))
  var size: Int = _

  var s: Calculator = _

  @Setup def setup = {
    s = Recursion.ana(CalculatorF.plusOnes)(size)
  }

  @Benchmark def basic: Double = CataBM.basic(CalculatorF.evalBasic)(s)
  @Benchmark def optimised: Double = CataBM.optimised(CalculatorF.evalBasic)(s)
}
