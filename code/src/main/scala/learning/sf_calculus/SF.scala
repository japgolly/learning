package learning.sf_calculus

import scala.annotation.tailrec

object Untyped {

  abstract class TermTree {
    final def apply(a: TermTree): TermTree =
      reduce($(this, a))
  }

  abstract class Term extends TermTree
  case object S extends Term
  case object F extends Term

  case class $(f: TermTree, a: TermTree) extends TermTree {
    override def toString = s"$f($a)"
  }

  /** Factorable form */
  object FF {
    def unapply(tt: TermTree): Option[TermTree] = tt match {
      case (S|F)
         | (S|F) $ _
         | (S|F) $ _ $ _ => Some(tt)
      // case _ => None
    }
  }

  @tailrec
  def reduce(tt: TermTree): TermTree = tt match {
    case S $ m $ n $ x               => reduce(m(x)(n(x)))
    case F $ (S|F) $ m $ n           => reduce(m)
    case F $ (FF(p) $ FF(q)) $ m $ n => reduce(n(p)(q))
    case _                           => tt
  }

}
