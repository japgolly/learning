package learning.profunctor_optics

// FunList[A, B, T] ≅ ∃n. Aⁿ x (Bⁿ → T)
sealed trait FunList[A, B, T]
object FunList {
  case class Done[A, B, T](done: T) extends FunList[A, B, T]
  case class More[A, B, T](a: A, next: FunList[A, B, B => T]) extends FunList[A, B, T]
}


final case class Forget[R, A, B](run: A => R) extends AnyVal {
  def contramap[C](f: C => A) = Forget[R, C, B](run compose f)
  def subst[C] = Forget[R, A, C](run)
}
object Forget {
  val _id = Forget(identity[Any])
  def id[A, B] = _id.asInstanceOf[Forget[A, A, B]]
}
