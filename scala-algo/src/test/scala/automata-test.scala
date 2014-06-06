package golly.algo.automata

import scala.language.reflectiveCalls
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
    val Q = Set("_", "B", "bO", "bo", "boo", "T")
    val Σ = Set('b', 'o', 'O', 't')
    val δ: (String, Char) => Option[String] = {
      case ("_", 'b') => Some("B")
      case ("B", 'o') => Some("bo")
      case ("B", 'O') => Some("bO")
      case ("bo", 'o') => Some("boo")
      case ("bo", 't') => Some("T")
      case ("boo", 't') => Some("T")
      case ("bO", 't') => Some("T")
      case _ => None
    }
    DFA(Q, Σ, δ, "_", Set("T"))
  }

  lazy val dfa2 = dfa.minimiseHopcroft
  lazy val dfai = dfa.toDFAia
  lazy val dfai2 = dfa2.minimiseHopcroft.toDFAia

  Console println dfa.show
  Console println dfa2.show
  Console println dfai.show
  Console println dfai2.show
//  Console println dfa.minimiseHopcroft.show
//  Console println dfa.minimiseHopcroft2.show
//  Console println dfa.minimiseHopcroft3.show
//  Console println dfa.minimiseHopcroft4.show

  //lazy val dfa2 = dfa.minimiseHopcroft
//  println(dfa2)
//  Console println dfai.show
//  Console println dfai2.show

  "NFA" should {
    "match 'cat'" in { nfa.run("cat".toList) must beTrue}
    "match 'cut'" in { nfa.run("cut".toList) must beTrue}
    "not match 'cc'" in { nfa.run("cc".toList) must beFalse}
    "not match 'catt'" in { nfa.run("catt".toList) must beFalse}
    "not match 'caut'" in { nfa.run("caut".toList) must beFalse}
  }

  def test(dfa: {def run(language: List[Char]): Boolean}) = {
    println(dfa)
    "match 'bot'" in { dfa.run("bot".toList) must beTrue}
    "match 'bOt'" in { dfa.run("bOt".toList) must beTrue}
    "match 'boot'" in { dfa.run("boot".toList) must beTrue}
    "not match 'bOot'" in { dfa.run("bOot".toList) must beFalse}
    "not match 'boOt'" in { dfa.run("boOt".toList) must beFalse}
    "not match 'bt'" in { dfa.run("bt".toList) must beFalse}
    "not match 'booot'" in { dfa.run("booot".toList) must beFalse}
    "not match 'bo'" in { dfa.run("bo".toList) must beFalse}
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
  "DFAi" should {test(dfai)}
  "DFAi2" should {test(dfai2)}
}