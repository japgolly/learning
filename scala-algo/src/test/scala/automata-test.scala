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
    val Q = Set("_", "B", "O1", "O2", "T")
    val Σ = Set('b', 'o', 't')
    val δ: (String, Char) => Option[String] = {
      case ("_", 'b') => Some("B")
      case ("B", 'o') => Some("O1")
      case ("O1", 'o') => Some("O2")
      case ("O1", 't') => Some("T")
      case ("O2", 't') => Some("T")
      case _ => None
    }
    DFA(Q, Σ, δ, "_", Set("T"))
  }

  "NFA" should {
    "match 'cat'" in { nfa.run("cat".toList) must beTrue}
    "match 'cut'" in { nfa.run("cut".toList) must beTrue}
    "not match 'cc'" in { nfa.run("cc".toList) must beFalse}
    "not match 'catt'" in { nfa.run("catt".toList) must beFalse}
    "not match 'caut'" in { nfa.run("caut".toList) must beFalse}
  }

  "DFA" should {
    "match 'bot'" in { dfa.run("bot".toList) must beTrue}
    "match 'boot'" in { dfa.run("boot".toList) must beTrue}
    "not match 'bt'" in { dfa.run("bt".toList) must beFalse}
    "not match 'boto'" in { dfa.run("boto".toList) must beFalse}
  }
}