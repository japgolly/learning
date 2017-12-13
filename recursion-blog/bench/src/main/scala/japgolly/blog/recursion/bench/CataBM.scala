package japgolly.blog.recursion.bench

import java.util.concurrent.TimeUnit
import japgolly.blog.recursion.data._
import japgolly.blog.recursion.definitions._
import japgolly.microlibs.recursion.Recursion
import matryoshka.data.{Fix => FixM}
import org.openjdk.jmh.annotations._

/** # Run complete. Total time: 00:03:04
  * Benchmark          (size)  Mode  Cnt    Score    Error  Units
  * CataBM.optimised    10000  avgt   30  195.576 ±  2.550  us/op
  * CataBM.basic        10000  avgt   30  358.676 ±  4.121  us/op
  * CataBM.matryoshka   10000  avgt   30  442.867 ± 21.570  us/op
  */
@Warmup(iterations = 10)
@Measurement(iterations = 10)
@Fork(3)
@BenchmarkMode(Array(Mode.AverageTime))
@OutputTimeUnit(TimeUnit.MICROSECONDS)
@State(Scope.Benchmark)
class CataBM {

//  @Param(Array("10", "100", "1000", "10000"))
  @Param(Array("10000"))
  var size: Int = _

  var s1: Calculator = _
  var s2: FixM[CalculatorF] = _

  @Setup def setup = {
    s1 = Recursion.ana(CalculatorF.plusOnes)(size)

    import _root_.matryoshka.implicits._
    s2 = size.ana[FixM[CalculatorF]](CalculatorF.plusOnes)
  }

  @Benchmark def optimised: Double =
    cata(CalculatorF.evalBasic)(s1)

  @Benchmark def basic: Double =
    cataUnoptimised(CalculatorF.evalBasic)(s1)

  @Benchmark def matryoshka: Double = {
    import _root_.matryoshka.implicits._
    s2.cata(CalculatorF.evalBasic)
  }
}
