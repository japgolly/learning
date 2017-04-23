package learning.profunctor_optics

object Optics {

  type Optic[F[_, _], S, T, A, B] = F[A, B] => F[S, T]

  trait OpticP[Constraint[_[_, _]], S, T, A, B] {
    def apply[P[_, _]: Constraint]: Optic[P, S, T, A, B]

    def compose[C2[_[_, _]], X, Y](that: OpticP[C2, A, B, X, Y]): OpticP[Constraint with C2, S, T, X, Y] = {
      val self = this
      type C3[P[_, _]] = Constraint[P] with C2[P]
      new OpticP[C3, S, T, X, Y] {
        def apply[P[_, _]](implicit P: C3[P]): Optic[P, S, T, X, Y] =
          self[P] compose that[P]
      }
    }
  }

  type Adapter[S, T, A, B] = OpticP[Profunctor, S, T, A, B]
  type Lens[S, T, A, B] = OpticP[Strong, S, T, A, B]
  type Prism[S, T, A, B] = OpticP[Choice, S, T, A, B]

  type Iso[S, A] = Adapter[S, S, A, A]

  // ===================================================================================================================
  import Instances._

  def lens[S, T, A, B](get: S => A, set: (S, B) => T): Lens[S, T, A, B] =
    new Lens[S, T, A, B] {
      override def apply[P[_, _]](implicit P: Strong[P]): P[A, B] => P[S, T] =
        pab => {
          val psaba: P[(S, A), (S, B)] = P.strongR[A, B, S](pab)
          val pst: P[S, T] = P.dimap(psaba)((s: S) => (s, get(s)), set.tupled)
          pst
        }
    }

  def prism[S, T, A, B](get: S => Either[T, A], set: B => T): Prism[S, T, A, B] =
    new Prism[S, T, A, B] {
      override def apply[P[_, _]](implicit P: Choice[P]): P[A, B] => P[S, T] =
        pab => {
          val ptata: P[Either[T, A], Either[T, B]] = P.choiceR[A, B, T](pab)
          val pst: P[S, T] = P.dimap(ptata)(get, _.fold(identity, set))
          pst
        }
    }

  // ===================================================================================================================

  //  viewP :: Optic (Forget a) s t a b -> s -> a
  //  viewP o = runForget (o (Forget id))
  def _view[S, T, A, B](optic: Optic[Forget[A, ?, ?], S, T, A, B])(s: S): A =
    optic(Forget.id).run(s)

  def view[Constraint[_[_, _]], S, T, A, B](optic: OpticP[Constraint, S, T, A, B])(s: S)(implicit c: Constraint[Forget[A, ?, ?]]): A =
    _view(optic.apply[Forget[A, ?, ?]])(s)

  // ===================================================================================================================

  def testLens[S, T, A, B](lens: Lens[S, T, A, B])(s: S)(f: A => B): T = {
    val x: (A => B) => (S => T) = lens[Function1]
    x(f)(s)
  }

  val egLens = lens[(Char, Int), (Char, String), Int, String](_._2, (ci, s) => (ci._1, s))

  val egPrism = prism[Option[Int], Option[String], Int, String](
    {
      case Some(i) => Right(i)
      case None => Left(None)
    },
    Some(_)
  )


  def main(args: Array[String]): Unit = {
    println()

    def testL(c: Char, i: Int): Unit = {
      val f = egLens[Function1]
      println("Lens over " + (c, i))
      println(s"mod: ${f("*" * _)((c, i))}")
      println(s"view: ${view(egLens)((c, i))}")
      println()
    }
    testL('x', 3)

    def testP(oi: Option[Int]): Unit = {
      val f = egPrism[Function1]
      println("Prism over " + oi)
      println(s"mod: ${f("*" * _)(oi)}")
      // println(s"view: ${view(egPrism)(oi)}") // No Choice[Forget A]
      println()
    }
    testP(None)
    testP(Some(3))
  }

}
