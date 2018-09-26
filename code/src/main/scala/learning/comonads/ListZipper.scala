package learning.comonads

case class ListZipper[A](left: List[A], focus: A, right: List[A]) {

  def map[B](f: A => B): ListZipper[B] =
    ListZipper(left map f, f(focus), right map f)

  def extend[B](f: ListZipper[A] => B): ListZipper[B] =
    duplicate.map(f)

  // performance lol
  def duplicate: ListZipper[ListZipper[A]] =
    ListZipper(
      left = left.indices.map(i => ListZipper(left.take(i - 1), left(i), left.drop(i + 1) ::: focus :: right)).toList,
      focus = this,
      right = right.indices.map(i => ListZipper(left ::: focus :: right.take(i), right(i), right.drop(i + 1))).toList
    )

  def moveRight: Option[ListZipper[A]] =
    right match {
      case Nil    => None
      case h :: t => Some(ListZipper(left :+ focus, h, t))
    }

  def update(a: A): ListZipper[A] =
    copy(focus = a)

  def toList: List[A] =
    left ::: focus :: right
}
