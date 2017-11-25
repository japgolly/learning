package japgolly.blog.recursion.ch02

import japgolly.blog.recursion.shared._
import japgolly.microlibs.recursion._
import scalaz.{Functor, \/, \/-}

object Ch02 {

  object Definitions {
    import scalaz.syntax.functor._

    def cata[F[_] : Functor, A, B](fAlgebra: F[A] => A)(f: Fix[F]): A =
      fAlgebra(f.unfix.map(cata(fAlgebra)))

    def cata2[F[_], A, B](algebra: F[A] => A)(f: Fix[F])(implicit F: Functor[F]): A = {
      var self: Fix[F] => A = null
      self = f => algebra(F.map(f.unfix)(self))
      self(f)
    }

  }
}