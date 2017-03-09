package golly.algo.automata

import scala.annotation.tailrec

object AsciiTable {

  def render(data: List[Vector[String]], topHeader: Boolean = true, leftHeader: Boolean = true): String =
    if (data.isEmpty) "" else {
      val cols = data.map(_.size).max
      val f = {
        val ws = (0 until cols).toList.map(i => data.map(_.applyOrElse(i, (_: Int) => "").size).max).map(w => s"%${w}s")
        val sep = "   "
        val x = if (leftHeader && cols > 1)
          ws.head + " | " + ws.tail.mkString(sep)
        else
          ws.mkString(sep)
        x + " |"
      }

      var lines = data.map(v => f.format(v: _*))
      val hr = "-" * lines.head.size
      if (topHeader && lines.size > 1) lines = lines.head :: hr :: lines.tail
      lines = hr :: lines ::: hr :: Nil

      lines mkString "\n"
    }
}

//object Implicits {
//  implicit class SetExt[A](s: Set[A]) extends AnyVal {
//  }
//}

// ============================================================================================================

object Util {
  def nameState[Q](q0: Q, accepts: Set[Q]): Q => String = {
    case q if q == q0 => s"$q→"
    case q if accepts contains q => s"$q*"
    case q => q + " "
  }
}
import Util._

case class IndexedSet[A](set: Set[A]) {
  val (byInd, toInd) = {
    val v = set.zipWithIndex
    val to = v.toVector.sortBy(_._2).map(_._1)
    (to, v.toMap)
  }
  def size = set.size
}

case class DFAi[Σ](states: Int, alphabet: Set[Σ], δ: (Int, Σ) => Option[Int], q0: Int, accepts: Set[Int]) {
  assert(states > 0)
  assert(q0 >= 0 && q0 < states)

  def run(language: List[Σ]): Boolean = {
    @tailrec
    def go(cur: Int, lang: List[Σ]): Boolean = lang match {
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

  def show = {
    val al = alphabet.toVector
    val hdr = "" +: al.map(_.toString)
    val body = (0 until states).toList.map(q => nameState(q0, accepts)(q) +: al.map(a => δ(q, a).fold(".")(_.toString)))
    s"DFA Size = ${states}x${alphabet.size}\n" + AsciiTable.render(hdr :: body)
  }

  def toDFA = DFA((0 until states).toSet, alphabet, δ, q0, accepts)
}



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

  def show = {
    val al = alphabet.toVector
    val hdr = "" +: al.map(_.toString)
    val body = states.toList.map(q => nameState(q0, accepts)(q) +: al.map(a => δ(q, a).fold(".")(_.toString)))
    s"DFA Size = ${states.size}x${alphabet.size}\n" + AsciiTable.render(hdr :: body)
  }

  def toDFAi = {
    val si = IndexedSet(states)
    val Δ: (Int, Σ) => Option[Int] = (stateI, letter) => δ(si.byInd(stateI), letter).map(si.toInd(_))
    DFAi(si.size, alphabet, Δ, si.toInd(q0), accepts.map(si.toInd))
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

  // http://en.wikipedia.org/wiki/DFA_minimization
  def minimiseHopcroft = {
    var p = Set(accepts, states -- accepts)
    //var w = Set(accepts) // wikipedia says
    var w = Set(states -- accepts) // trumping wikipedia here
    while (w.nonEmpty) {
      val a = w.head
      w -= a
//      println(s"A = $a, W = $w, P = $p")
      for (c <- alphabet) {
        val x = δInv(c)(a)
//        println(s"  Set of states for which a transition on '$c' leads to a state in $a  =  $x")
        var p2 = p
        for {
          y <- p
          intersection = x & y if intersection.nonEmpty
          compliment = y -- x if compliment.nonEmpty
        } {
//          println(s"  P2 = $p2 | INT = $intersection | COM = $compliment | X = $x | Y = $y")
          p2 = p2 - y + intersection + compliment
//          println("  P2 = "+p2)
          if (w contains y)
            w = w - y + intersection + compliment
          else
            w += smaller(intersection, compliment)
        }
        p = p2
      }
//      println()
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

  def println(s: => Any = ""): Unit = ()// Console.println(s)

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
