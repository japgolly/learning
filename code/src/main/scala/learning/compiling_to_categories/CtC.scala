package learning.compiling_to_categories

object CT {
  type Id[A] = A

  trait Category[~>[_, _]] {
    def id[A]: A ~> A
    def compose[A, B, C]: (B ~> C) => (A ~> B) => (A ~> C)
  }

  trait Cartesian[~>[_, _]] {
    def fork[A, B, C]: (A ~> B) => (A ~> C) => (A ~> (B, C))
    def exl[A, B]: ((A, B)) ~> A
//    def exr[A, B]: ((A, B)) ~> B
    def exr[A, B]: ~>[(A, B), B]
  }

  trait ClosedG[~>[_, _], |=>[_, _]] {
    def apply[A, B]: ((A |=> B), A) ~> B
    def curry[A, B, C]: ((A, B) ~> C) => (A ~> (B |=> C))
    def uncurry[A, B, C]: (A ~> (B |=> C)) => ((A, B) ~> C)
  }

  type Closed[F[_, _]] = ClosedG[F, Function1]

  type CCC[F[_, _]] = Category[F] with Cartesian[F] with Closed[F]

  trait Terminal[~>[_, _]] {
    def terminate[A]: A ~> Unit
  }
}
import CT._

/** IC */
object TMP {

  case class HasDelta[A, D](sub: (A, A) => D, add: (A, D) => A, nil: D) {
    def merge[B, DB](that: HasDelta[B, DB]): HasDelta[(A, B), (D, DB)] =
      HasDelta.merge(this, that)
  }

  object HasDelta {
    def byUnivEq[A]: HasDelta[A, Option[A]] =
      apply[A, Option[A]](
        (x, y) => if (x == y) None else Some(y),
        (x, y) => y getOrElse x,
        None)

    def merge[A, DA, B, DB](hdA: HasDelta[A, DA], hdB: HasDelta[B, DB]): HasDelta[(A, B), (DA, DB)] =
      apply[(A, B), (DA, DB)](
        { case ((al, bl), (a, b)) => (hdA.sub(al, a), hdB.sub(bl, b)) },
        { case ((a, b), (da, db)) => (hdA.add(a, da), hdB.add(b, db)) },
        (hdA.nil, hdB.nil))

    def liftA2[I, A, B, C](f: (A, B) => C)(fa: I => A, fb: I => B):  I => C =
      i => f(fa(i), fb(i))

    def fn[A, B, DB](hdB: HasDelta[B, DB]): HasDelta[A => B, A => DB] =
      apply(liftA2(hdB.sub), liftA2(hdB.add), _ => hdB.nil)

  }

  /*
  case class DelX[A, DA, B, DB](f: HasDelta[A, DA] => HasDelta[B, DB])

  object DelX {
    def cc[DA, DB] = {
      type DelX2[A, B] = DelX[A, DA, B, DB]
      def DelX2[A, B](f: HasDelta[A, DA] => HasDelta[B, DB]): DelX2[A, B] = DelX(f)

      type OMG2[A, B] = HasDelta[(A, B), (DA, DB)]
      type OMGa[A, B] = HasDelta[A, DB]
      def C: Cartesian[HasDelta] = ???

      new Cartesian[DelX2] {
        override def fork[A, B, C] = ab => ac => ???
        override def exl[A, B]: DelX2[(A, B), A] = DelX2(??? : HasDelta[(A, B), DA] => HasDelta[A, DB])
        override def exr[A, B] = ???
      }
    }

    // ((X, Y)) ~> X
    // X = HasDelta[(A, B), DA]
    // Y = HasDelta[A, DB]
  }
  */

}

// █████████████████████████████████████████████████████████████████████████████████████████████████████████████████████

object TMP2 {

  trait HasDelta[A] {
    type D
    val add: (A, D) => A
    val sub: (A, A) => D
    val nil: D
  }

  object HasDelta {

    def apply[A, Δ](_add: (A, Δ) => A,
                    _sub: (A, A) => Δ,
                    _nil: Δ): HasDelta[A] =
      new HasDelta[A] {
        override type D = Δ
        override val add = _add
        override val sub = _sub
        override val nil = _nil
      }

    def byUnivEq[A]: HasDelta[A] =
      apply[A, Option[A]](
        (x, y) => y getOrElse x,
        (x, y) => if (x == y) None else Some(y),
        None)

    def merge[A, B](A: HasDelta[A], B: HasDelta[B]): HasDelta[(A, B)] =
      apply[(A, B), (A.D, B.D)](
        { case ((a, b), (da, db)) => (A.add(a, da), B.add(b, db)) },
        { case ((al, bl), (a, b)) => (A.sub(al, a), B.sub(bl, b)) },
        (A.nil, B.nil))

//    def splitl[A, B](h: HasDelta[(A, B)] {type }): HasDelta[A] =
//      apply[A, h.(A.D, B.D)](
//        { case ((a, b), (da, db)) => (A.add(a, da), B.add(b, db)) },
//        { case ((al, bl), (a, b)) => (A.sub(al, a), B.sub(bl, b)) },
//        (A.nil, B.nil))

    def liftA2[I, A, B, C](f: (A, B) => C)(fa: I => A, fb: I => B):  I => C =
      i => f(fa(i), fb(i))

    def fn[A, B](B: HasDelta[B]): HasDelta[A => B] =
      apply[A => B, A => B.D](liftA2(B.add)(_, _), liftA2(B.sub)(_, _), _ => B.nil)

    type HDC[A, B] = HasDelta[(A, B)]
    object HDC extends Cartesian[HDC] {
      override def fork[A, B, C] = ab => ac => ???
//      override def exl[A, B]: HasDelta[(A, B)] => HasDelta[A] = ??? //HasDelta[((A, B), A), Unit](???, ???, ???)
      override def exl[A, B] = ???
      override def exr[A, B]: HasDelta[((A, B), B)] = ???
    }
  }

  trait DelX[A, B] {
    type D[_]
    val fn: D[A] => D[B]
  }
  object DelX {
    def apply[Δ[_], A, B](f: Δ[A] => Δ[B]): DelX[A, B] = new DelX[A, B] {
      override type D[X] = Δ[X]
      override val fn = f
    }
    def simple[A, B](f: A => B): DelX[A, B] = apply[Id, A, B](f)

    object ct extends Cartesian[DelX] {
      override def fork[A, B, C] = ab => ac => ???
      override def exl[A, B]: DelX[(A, B), A] = simple(_._1)
      override def exr[A, B]: DelX[(A, B), B] = simple(_._2)
    }
  }

}

