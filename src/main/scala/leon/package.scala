import scala.collection.generic.CanBuildFrom

/* Copyright 2009-2016 EPFL, Lausanne */

/** Core package of the Leon system 
  *
  * Provides the basic types and definitions for the Leon system.
  */
package object leon {
  implicit class BooleanToOption(cond: Boolean) {
    def option[A](v: => A) = if (cond) Some(v) else None
  }

  implicit class MonadicSeq[A, S[X]<: Seq[X]](s: S[A]) {
    def mapM[B](f: A => Option[B])(implicit cbf: CanBuildFrom[S[A], B, S[B]]): Option[S[B]] = {
      if (s.isEmpty) Some(cbf().result())
      else {
        for {
          h <- f(s.head)
          t <- s.tail.mapM(f)
        } yield (h +: t).asInstanceOf[S[B]]
      }
    }
  }

}
