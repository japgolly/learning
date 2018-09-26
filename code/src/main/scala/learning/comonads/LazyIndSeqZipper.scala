package learning.comonads

case class LazyIndSeqZipper[A](elements: Int, focus: Int, view: Int => A) {

  // O(1)
  def extract: A =
    view(focus)

  // O(1)
  def map[B](f: A => B): LazyIndSeqZipper[B] =
    copy(view = f compose view)

  // O(1)
  def duplicate: LazyIndSeqZipper[LazyIndSeqZipper[A]] =
    copy(view = LazyIndSeqZipper(elements, _, view))

  // O(1)
  def extend[B](f: LazyIndSeqZipper[A] => B): LazyIndSeqZipper[B] =
    duplicate.map(f)

  def iterator(): Iterator[A] =
    (0 until elements).iterator.map(view)

  // O(N)
  def toVector: Vector[A] =
    iterator().toVector

  override def toString: String =
    ((toVector.take(focus).map(_.toString) :+ s"[${extract}]") ++ toVector.drop(focus + 1)).mkString(", ")
}

object LazyIndSeqZipper {

  def from[A](h: A, t: IndexedSeq[A]): LazyIndSeqZipper[A] =
    LazyIndSeqZipper[A](
      t.length + 1,
      0,
      i => if (i == 0) h else t(i - 1))
}
