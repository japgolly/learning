package japgolly.blog.recursion

import scalaz.Functor
import scalaz.syntax.functor._

package object definitions {

  // ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  // Chapter 1

  // Typical definition of Fix - causes boxing
  final case class BoxedFix[F[_]](unfix: F[Fix[F]])

  // Optimised definition of Fix - avoids boxing
  val Fix: FixModule = FixImpl
  type Fix[F[_]] = Fix.Fix[F]

  // Add an .unfix method to Fix types so that it behaves the same as our original boxed version
  @inline implicit class FixOps[F[_]](private val self: Fix[F]) extends AnyVal {
    @inline def unfix: F[Fix[F]] =
      Fix.unfix(self)
  }


  // ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  // Chapter 2

  def cataUnoptimised[F[_] : Functor, A, B](fAlgebra: F[A] => A)(f: Fix[F]): A =
    fAlgebra(f.unfix.map(cataUnoptimised(fAlgebra)))

  type FAlgebra[F[_], A] = F[A] => A

  def cata[F[_], A, B](algebra: FAlgebra[F, A])(f: Fix[F])(implicit F: Functor[F]): A = {
    var self: Fix[F] => A = null
    self = f => algebra(F.map(f.unfix)(self))
    self(f)
  }

  def falgebraZip[F[_], A, B](fa: FAlgebra[F, A],
                              fb: FAlgebra[F, B])
                             (implicit F: Functor[F]): FAlgebra[F, (A, B)] =
    fab => {
      val a = fa(fab.map(_._1))
      val b = fb(fab.map(_._2))
      (a, b)
    }
}
