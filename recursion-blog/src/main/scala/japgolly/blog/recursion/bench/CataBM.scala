package japgolly.blog.recursion.bench

import java.util.concurrent.TimeUnit
import japgolly.blog.recursion.shared._
import japgolly.microlibs.recursion._
import matryoshka.data.Mu
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

@Warmup(iterations = 20)
@Measurement(iterations = 20)
@Fork(1)
@BenchmarkMode(Array(Mode.AverageTime))
@OutputTimeUnit(TimeUnit.MICROSECONDS)
@State(Scope.Benchmark)
class CataBM {

//  @Param(Array("10", "100", "1000", "10000"))
  @Param(Array("10000"))
  var size: Int = _

  var s1: Calculator = _
  var s2: Mu[CalculatorF] = _

  @Setup def setup = {
    s1 = Recursion.ana(CalculatorF.plusOnes)(size)

    import _root_.matryoshka.implicits._
    s2 = size.ana[Mu[CalculatorF]](CalculatorF.plusOnes)
  }

  @Benchmark def basic: Double = CataBM.basic(CalculatorF.evalBasic)(s1)
  @Benchmark def optimised: Double = CataBM.optimised(CalculatorF.evalBasic)(s1)

  @Benchmark def matryoshka: Double = {
    import _root_.matryoshka.implicits._
    s2.cata(CalculatorF.evalBasic)
  }
}
