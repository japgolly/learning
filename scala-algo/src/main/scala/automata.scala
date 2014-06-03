package golly.algo.automata

import scala.annotation.tailrec

// ============================================================================================================

case class DFA[Q, Σ](states: Set[Q], alphabet: Set[Σ], δ: (Q, Σ) => Option[Q], q0: Q, accepts: Set[Q]) {

  def run(language: List[Σ]): Boolean = {

    @tailrec
    def go(cur: Q, lang: List[Σ]): Boolean = lang match {
      case Nil =>
        accepts contains cur
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

case class NFA[Q, Σ](states: Set[Q], alphabet: Set[Σ], δ: (Q, Σ) => Set[Q], q0: Q, accepts: Set[Q]) {

  def println(s: => Any = ""): Unit = ()// Console.println(s)

  def run(language: List[Σ]): Boolean = {

    def Δ(cur: Set[Q], σ: Σ) = cur.foldLeft(Set.empty[Q])((r, q) => r ++ δ(q, σ))

    @tailrec
    def go(cur: Set[Q], lang: List[Σ]): Boolean = {
      println(s"$cur ⇐ $lang")
      lang match {
        case Nil =>
          accepts.exists(q => cur.exists(_ == q))
        case h :: t =>
          val next = Δ(cur, h)
          if (next.isEmpty)
            false
          else
            go(next, t)
      }
    }

    println()
    val r = go(Set(q0), language)
    println(s"  ⇒ $r")
    r
  }
}
