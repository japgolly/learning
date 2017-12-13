package japgolly.blog.recursion.definitions

import japgolly.blog.recursion.definitions

// Originally from:
//   https://github.com/scalaz/scalaz/pull/1472/files

// Benchmark results:
//   https://github.com/japgolly/microlibs-scala/commit/c2c1f8adaa9c9166ed6c10a0c3c09cfdbc0c8d58

sealed trait FixModule {
  type Fix[F[_]]

  def apply[F[_]](f: F[definitions.Fix[F]]): Fix[F]
  def unfix[F[_]](f: Fix[F]): F[definitions.Fix[F]]
}

private[definitions] object FixImpl extends FixModule {
  override type Fix[F[_]] = F[definitions.Fix[F]]

  override def apply[F[_]](f: F[definitions.Fix[F]]): Fix[F] = f
  override def unfix[F[_]](f: Fix[F]): F[definitions.Fix[F]] = f
}
