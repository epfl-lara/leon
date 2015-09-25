/* Copyright 2009-2015 EPFL, Lausanne */
import leon.collection._
object Nested1 {

  def foo[A](i: List[A]): BigInt = {
    val n = i
    def rec1[B](j: List[B]) = j ++ j
    def rec2[C](l: List[C], j: BigInt) = {
      require(l.nonEmpty)
      def rec3(k: C) = k :: rec1[C](l)
      rec3(l.head).size + j + n.size + i.size
    }
    rec2(List(true, true, false), 2)
  } ensuring(i.size + 7 == _)

}

// vim: set ts=4 sw=4 et:
