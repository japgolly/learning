package learning.profunctor_optics

object OpticsFn {

  type Optic[S, T, A, B] = (A => B) => S => T

  def lens[S, T, A, B](get: S => A, set: (S, B) => T): Optic[S, T, A, B] =
    mod => s => set(s, mod(get(s)))

  def prism[S, T, A, B](get: S => Either[T, A], set: B => T): Optic[S, T, A, B] =
    mod => s => get(s) match {
      case Right(a) => set(mod(a))
      case Left(t) => t
    }

  def compose[S, T, A, B, X, Y](f: Optic[S, T, A, B], g: Optic[A, B, X, Y]): Optic[S, T, X, Y] =
    f compose g

}
