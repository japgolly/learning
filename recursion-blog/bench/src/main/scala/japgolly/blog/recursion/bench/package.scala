package japgolly.blog.recursion

import japgolly.blog.recursion.definitions.Fix
import japgolly.microlibs.recursion.{Fix => Fix2}

package object bench {

  // These two definitions are the same
  implicit def japgollyBlogToJapgollyLib[F[_]](f: Fix[F]): Fix2[F] = f.asInstanceOf[Fix2[F]]
  implicit def japgollyLibToJapgollyBlog[F[_]](f: Fix2[F]): Fix[F] = f.asInstanceOf[Fix[F]]
}
