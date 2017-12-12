package japgolly.blog.recursion

import japgolly.blog.recursion.definitions.Fix

package object data {

  type IntList       = Fix[IntListF]
  val  IntList       = IntListF.IntList
  type BinaryTree[A] = Fix[BinaryTreeF[A, ?]]
  type Json          = Fix[JsonF]
  val  Json          = JsonF.Json
  type Calculator    = Fix[CalculatorF]
  val  Calculator    = CalculatorF.Calculator

  def assertEqual[A](name: String, actual: A, expect: A): Unit = {
    println(s"$name: $actual should be $expect")
    assert(actual == expect) // univeq...
  }
}
