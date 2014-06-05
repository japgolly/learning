package golly.algo.automata

import org.specs2.mutable._
import org.specs2.ScalaCheck

class AutomataTest extends Specification with ScalaCheck {

  sequential

  lazy val nfa = {
    val Q = Set("_", "C/A", "C/U", "A", "U", "T")
    val Σ = Set('c', 'a', 'u', 't')
    val δ: (String, Char) => Set[String] = {
      case ("_", 'c') => Set("C/A", "C/U")
      case ("C/A", 'a') => Set("A")
      case ("C/U", 'u') => Set("U")
      case ("A", 't') => Set("T")
      case ("U", 't') => Set("T")
      case _ => Set.empty
    }
    NFA(Q, Σ, δ, "_", Set("T"))
  }

  lazy val dfa = {
    val Q = Set("_", "B", "O1", "O1U", "O2", "T")
    val Σ = Set('b', 'o', 'O', 't')
    val δ: (String, Char) => Option[String] = {
      case ("_", 'b') => Some("B")
      case ("B", 'o') => Some("O1")
      case ("B", 'O') => Some("O1U")
      case ("O1", 'o') => Some("O2")
      case ("O1", 't') => Some("T")
      case ("O1U", 't') => Some("T")
      case ("O2", 't') => Some("T")
      case _ => None
    }
    DFA(Q, Σ, δ, "_", Set("T"))
  }

  lazy val dfa2 = dfa.minimiseHopcroft4
//  println(dfa2)

  "NFA" should {
    "match 'cat'" in { nfa.run("cat".toList) must beTrue}
    "match 'cut'" in { nfa.run("cut".toList) must beTrue}
    "not match 'cc'" in { nfa.run("cc".toList) must beFalse}
    "not match 'catt'" in { nfa.run("catt".toList) must beFalse}
    "not match 'caut'" in { nfa.run("caut".toList) must beFalse}
  }

  def test(dfa: DFA[String, Char]) = {
    println(dfa)
    "match 'bot'" in { dfa.run("bot".toList) must beTrue}
    "match 'bot'" in { dfa.run("bot".toList) must beTrue}
    "match 'bOt'" in { dfa.run("bOt".toList) must beTrue}
    "match 'boot'" in { dfa.run("boot".toList) must beTrue}
    "not match 'bOot'" in { dfa.run("bOot".toList) must beFalse}
    "not match 'boOt'" in { dfa.run("boOt".toList) must beFalse}
    "not match 'bt'" in { dfa.run("bt".toList) must beFalse}
    "not match 'boto'" in { dfa.run("boto".toList) must beFalse}
  }

  "DFA" should {
    "δInv" in {
      var errs = List.empty[String]
      for {q <- dfa.states; a <- dfa.alphabet; q2 <- dfa.δ(q, a)} {
        val t = dfa.δInv(a)(Set(q2))
        if (!t.contains(q) || t.map(dfa.δ(_, a) == q).forall(b => b))
          errs ::= s"\n  δ($q, $a) = $q2, δInv = $t"
      }
      errs must beEmpty
    }
    test(dfa)
  }
  "DFA2" should {test(dfa2)}
}