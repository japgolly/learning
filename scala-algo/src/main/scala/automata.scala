package golly.algo.automata

import scala.annotation.tailrec
//import scalaz.{Order, ISet}

trait SetT[S[_], A] {
  def contains(s: S[A], a: A): Boolean
  def isEmpty(s: S[A]): Boolean
  def empty: S[A]
  def point(a: A): S[A]
  def union(a: S[A], b: S[A]): S[A]
  def exists(s: S[A], f: A => Boolean): Boolean
  def fold[B](s: S[A], b: B)(f: (B, A) => B): B
}

object SetT {
//  implicit def ISetT[A: Order]: SetT[ISet, A] = new SetT[ISet, A] {
//    override def contains(s: ISet[A], a: A) = s contains a
//  }

  implicit def ScalaSetT[A]: SetT[Set, A] = new SetT[Set, A] {
    override def contains(s: Set[A], a: A) = s contains a
    override def isEmpty(s: Set[A]) = s.isEmpty
    override def empty = Set.empty[A]
    override def point(a: A) = Set(a)
    override def union(a: Set[A], b: Set[A]) = a ++ b
    override def exists(s: Set[A], f: A => Boolean) = s exists f
    override def fold[B](s: Set[A], b: B)(f: (B, A) => B) = s.foldLeft(b)(f)
  }
}

// ============================================================================================================

case class DFA[S[_], Q, Σ](states: S[Q], alphabet: S[Σ], δ: (Q, Σ) => Option[Q], q0: Q, accepts: S[Q])(implicit S: SetT[S, Q]) {

  def run(language: List[Σ]): Boolean = {

    @tailrec
    def go(cur: Q, lang: List[Σ]): Boolean = lang match {
      case Nil =>
        S.contains(accepts, cur)
      case h :: t =>
        δ(cur, h) match {
          case Some(next) => go(next, t)
          case None => false
        }
    }

    go(q0, language)
  }
}

// ============================================================================================================

case class NFA[S[_], Q, Σ](states: S[Q], alphabet: S[Σ], δ: (Q, Σ) => S[Q], q0: Q, accepts: S[Q])(implicit S: SetT[S, Q]) {

  def println(s: => Any = ""): Unit = ()// Console.println(s)

  def run(language: List[Σ]): Boolean = {

    def Δ(cur: S[Q], σ: Σ) = S.fold(cur, S.empty)((r, q) => S.union(r, δ(q, σ)))

    @tailrec
    def go(cur: S[Q], lang: List[Σ]): Boolean = {
      println(s"$cur ⇐ $lang")
      lang match {
        case Nil =>
          S.exists(accepts, q => S.exists(cur, _ == q))
        case h :: t =>
          val next = Δ(cur, h)
          if (S isEmpty next)
            false
          else
            go(next, t)
      }
    }

    println()
    val r = go(S point q0, language)
    println(s"  ⇒ $r")
    r
  }

  def toDFA: DFA[S, Q, Σ] == {

  }
}
