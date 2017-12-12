package japgolly.blog.recursion.ch02

import japgolly.blog.recursion.data._
import japgolly.blog.recursion.definitions.{Fix, FAlgebra, cata, falgebraZip}
import scalaz.Functor

object BasicExamples {

  val listSum: FAlgebra[IntListF, Int] = {
    case IntListF.Cons(h, t) => h + t
    case IntListF.Nil        => 0
  }

  val listSumVerbose: IntListF[Int] => Int = {
    case IntListF.Cons(h, t) => h + t
    //                 |  |
    // Int by definition  |
    //                    Sum of tail (Int)
    case IntListF.Nil => 0
  }

  def sumThisListPlease(list: IntList): Int =
    cata(listSum)(list)

  val listLength: FAlgebra[IntListF, Int] = {
    case IntListF.Cons(_, t) => 1 + t
    case IntListF.Nil        => 0
  }

  val listLengthVerbose: IntListF[Int] => Int = {
    case IntListF.Cons(_, t) => 1 + t
    //                    |     |
    //                    |     Add 1 for this element
    // Length of tail (Int)
    case IntListF.Nil => 0
  }

  val binaryTreeNodeCount: FAlgebra[BinaryTreeF[Any, ?], Int] = {
    case BinaryTreeF.Node(left, _, right) => left + 1 + right
    case BinaryTreeF.Leaf                 => 0
  }

  val binaryTreeMaxDepth: FAlgebra[BinaryTreeF[Any, ?], Int] = {
    case BinaryTreeF.Node(left, _, right) => left.max(right) + 1
    case BinaryTreeF.Leaf                 => 0
  }

  def binaryTreeSum[N](implicit N: Numeric[N]): FAlgebra[BinaryTreeF[N, ?], N] = {
    case BinaryTreeF.Node(left, n, right) => N.plus(left, N.plus(n, right))
    case BinaryTreeF.Leaf                 => N.zero
  }

  def escapeString(s: String): String =
    // Something along these lines...
    s.iterator.flatMap {
      case c@('"' | '\\') => '\\' :: c :: Nil
      case c              => c :: Nil
    }.mkString("\"", "", "\"")

  val jsonToString: FAlgebra[JsonF, String] = {
    case JsonF.Null        => "null"
    case JsonF.Bool(b)     => b.toString
    case JsonF.Num(n)      => n.toString
    case JsonF.Str(s)      => escapeString(s)
    case JsonF.Arr(values) => values.mkString("[", ",", "]")
    case JsonF.Obj(fields) => fields.iterator.map { case (k, v) => k + ":" + v }.mkString("{", ",", "}")
  }

  val jsonToStringSB: FAlgebra[JsonF, StringBuilder => Unit] = {
    case JsonF.Null        => _ append "null"
    case JsonF.Bool(b)     => _ append b.toString
    case JsonF.Num(n)      => _ append n.toString
    case JsonF.Str(s)      => _ append escapeString(s)
    case JsonF.Arr(values) => sb => {
      sb append '['
      for (v <- values) v(sb)
      sb append ']'
    }
    case JsonF.Obj(fields) => sb => {
      sb append '{'
      for ((k, v) <- fields) {
        sb append k
        sb append ':'
        v(sb)
      }
      sb append '}'
    }
  }

  def jsonToStringBuilderUsage(json: Json): String = {
    val sbToUnit = cata(jsonToStringSB)(json)
    val sb = new StringBuilder
    sbToUnit(sb)
    sb.toString()
  }
}

// █████████████████████████████████████████████████████████████████████████████████████████████████████████████████████

object FileSystem {

  object Before {
    sealed trait Entry
    final case class Dir(files: Map[String, Entry]) extends Entry
    final case class File(size: Long) extends Entry

    // Example of 3 files:
    // 1. /usr/bin/find
    // 2. /usr/bin/ls
    // 3. /tmp/example.tmp
    val example =
      Dir(Map(
        "usr" -> Dir(Map(
          "bin" -> Dir(Map(
            "find" -> File(197360),
            "ls" -> File(133688))))),
        "tmp" -> Dir(Map(
          "example.tmp" -> File(12)))))

    // ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    object V1 {
      def totalFileSize(e: Entry): Long = e match {
        case File(s) => s
        case Dir(fs) => fs.values.foldLeft(0L)(_ + totalFileSize(_))
      }

      def countFiles(e: Entry): Int = e match {
        case File(_) => 1
        case Dir(fs) => fs.values.foldLeft(0)(_ + countFiles(_))
      }

      def countDirs(e: Entry): Int = e match {
        case File(_) => 0
        case Dir(fs) => fs.values.foldLeft(1)(_ + countDirs(_))
      }

      final case class Stats(totalSize: Long, files: Int, dirs: Int)

      // Traverses FS 3 times! Grossly inefficient
      def stats(e: Entry): Stats =
        Stats(totalFileSize(e), countFiles(e), countDirs(e))
    }

    // ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    object V2 {
      final case class Stats(totalSize: Long, files: Int, dirs: Int)

      def stats(e: Entry): Stats = e match {
        case File(fileSize) =>
          Stats(fileSize, 1, 0)
        case Dir(fs) =>
          fs.values.foldLeft(Stats(0, 0, 0)) { (statsAcc, entry) =>
            val b = stats(entry)
            Stats(
              statsAcc.totalSize + b.totalSize,
              statsAcc.files + b.files,
              statsAcc.dirs + b.dirs)
          }
      }

      def totalFileSize(e: Entry): Long =
        stats(e).totalSize

      def countFiles(e: Entry): Int =
        stats(e).files

      def countDirs(e: Entry): Int =
        stats(e).dirs
    }
  }

  // ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  object After {
    sealed trait EntryF[+F]
    final case class Dir[F](files: Map[String, F]) extends EntryF[F]
    final case class File(size: Long) extends EntryF[Nothing]

    object EntryF {
      implicit val functor: Functor[EntryF] = new Functor[EntryF] {
        override def map[A, B](fa: EntryF[A])(f: A => B): EntryF[B] = fa match {
          case f: File => f
          case Dir(fs) => Dir(fs.map { case (k, v) => (k, f(v)) })
        }
      }
    }

    type Entry = Fix[EntryF]
    object Entry {
      def apply(f: EntryF[Entry]): Entry = Fix(f)
      def file(s: Long): Entry = apply(File(s))
      def dir(es: (String, Entry)*): Entry = apply(Dir(es.toMap))
    }

    // Example of 3 files:
    // 1. /usr/bin/find
    // 2. /usr/bin/ls
    // 3. /tmp/example.tmp
    val example =
      Entry.dir(
        "usr" -> Entry.dir(
          "bin" -> Entry.dir(
            "find" -> Entry.file(197360),
            "ls" -> Entry.file(133688))),
        "tmp" -> Entry.dir(
          "example.tmp" -> Entry.file(12)))

    val totalFileSize: FAlgebra[EntryF, Long] = {
      case File(s) => s
      case Dir(fs) => fs.values.sum
    }

    val countFiles: FAlgebra[EntryF, Int] = {
      case File(_) => 1
      case Dir(fs) => fs.values.sum
    }

    val countDirs: FAlgebra[EntryF, Int] = {
      case File(_) => 0
      case Dir(fs) => fs.values.sum + 1
    }

    val statsAlg: FAlgebra[EntryF, (Long, (Int, Int))] =
      falgebraZip(totalFileSize, falgebraZip(countFiles, countDirs))

    final case class Stats(totalSize: Long, files: Int, dirs: Int)

    def stats(e: Entry): Stats = {
      val (totalSize, (files, dirs)) = cata(statsAlg)(e)
      Stats(totalSize, files, dirs)
    }

  }


}
