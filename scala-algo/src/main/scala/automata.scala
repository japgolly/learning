package golly.algo.automata

import scala.annotation.tailrec

//object Implicits {
//  implicit class SetExt[A](s: Set[A]) extends AnyVal {
//  }
//}

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

  def smaller[A](a: Set[A], b: Set[A]) = if (a.size <= b.size) a else b

  def δInv: Σ => Set[Q] => Set[Q] =
    a => qs => states.filter(δ(_, a).fold(false)(qs contains _))

  def split(b: Set[Q], s: Set[Q], a: Σ) = {
    println(s"  δ⁻¹($a, $s) = ${δInv(a)(s)}")
    val x = b & δInv(a)(s)
    val y = states -- x
    (b & x, b & y)
  }

  // http://www.dcc.fc.up.pt/dcc/Pubs/TReports/TR07/dcc-2007-03.pdf
  def minimiseHopcroft2 = {
    var p = Set(accepts, states -- accepts)
    var l = Set(accepts)
    while (l.nonEmpty) {
      val s = l.head
      l -= s
      for (a <- alphabet) {
        var p2 = p
        for (b <- p) {
          val (b1,b2) = split(b, s, a)
          if (b1.nonEmpty && b2.nonEmpty) {
            p2 = p2 - b + b1 + b2
            l += smaller(b1, b2)
          }
        }
        p = p2
      }
    }

    minimiseWith(p)
  }

  // http://en.wikipedia.org/wiki/DFA_minimization
  def minimiseHopcroft = {
    var p = Set(accepts, states -- accepts)
    var w = Set(accepts)
    while (w.nonEmpty) {
      val a = w.head
      w -= a
      println(s"A = $a, W = $w, P = $p")
      for (c <- alphabet) {
        val x = δInv(c)(a)
        //println(s"Set of states for which a transition on '$c' leads to a state in $a  =  $x")
        var p2 = p
        for {
          y <- p
          intersection = x & y if intersection.nonEmpty
          compliment = y -- x if compliment.nonEmpty
        } {
          println(s"  P2 = $p2 | INT = $intersection | COM = $compliment | X = $x | Y = $y")
          p2 = p2 - y + intersection + compliment
          println("  P2 = "+p2)
          if (w contains y)
            w = w - y + intersection + compliment
          else
            w += smaller(intersection, compliment)
        }
        p = p2
      }
    }

    minimiseWith(p)
  }

  def minimiseHopcroft4 = {
    val c0 = accepts
    val c1 = states -- accepts
    var p = Set(c0, c1)
    var l = Set(smaller(c0, c1))
    while (l.nonEmpty) {
      val c = l.head
      l -= c
      println(s"C = $c, L = $l, P = $p")
      for (a <- alphabet) {
        println(s"---> P = $p")
        for (b <- p) {
          println(s"       b = $b")
          val (b1,b2) = split(b, c, a)
//          println(s"  a = $a, b = $b, b1|2 = $b1|$b2, P = $p")
          if (b1.nonEmpty) {
            p = p - b + b1 + b2
            if (l(b))
              l = l - b + b1 + b2
            else
              l += smaller(b1, b2)
          }
        }
      }
    }

    minimiseWith(p)
  }

  // http://computerlabor.math.uni-kiel.de/stochastik/colloquium08/slides/carton.pdf
  def minimiseHopcroft3 = {
    val F = accepts
    val Fc = states -- accepts
    val minFFc = smaller(F, Fc)
    var p = Set(F, Fc)
    var w = alphabet.map(a => (minFFc, a))
    while (w.nonEmpty) {
      val pair = w.head
      w -= pair
      val (c, a) = pair
      println(s"C = $c, a = $a, W = $w, P = $p")

      var p2 = p
      for (b <- p) {
        val (b1, b2) = split(b, c, a)
        if (b1.nonEmpty && b2.nonEmpty) {
          p2 = p2 - b + b1 + b2
          for (bb <- alphabet)
            if (w.contains((b, bb)))
              w = w - ((b, bb)) + ((b1, bb)) + ((b2, bb))
            else
              w += ((smaller(b1, b2), bb))
        }
      }
      p = p2
    }

    minimiseWith(p)
  }

  def minimiseWith(equivilentStates: Set[Set[Q]]) = {
    println(s"minimiseWith: $equivilentStates")
    val dups = equivilentStates.filter(_.size > 1)
    val dupToUniq = dups.foldLeft(Map.empty[Q, Q])((m, qs) => {
      val h = qs.head
      m ++ (qs - h).map(_ -> h).toMap
    })
    println(s"minimiseWith: $dupToUniq")
    val dupQs = dupToUniq.keySet
    def fix(q: Q): Q = dupToUniq.getOrElse(q, q)
    val δ2: (Q, Σ) => Option[Q] = δ(_,_) map fix
    DFA(states -- dupQs, alphabet, δ2, fix(q0), accepts -- dupQs)
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
