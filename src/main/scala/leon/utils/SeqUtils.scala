/* Copyright 2009-2015 EPFL, Lausanne */

package leon.utils

import scala.collection.mutable.ArrayBuffer

object SeqUtils {
  type Tuple[T] = Seq[T]


  def cartesianProduct[T](seqs: Tuple[Seq[T]]): Seq[Tuple[T]] = {
    val sizes = seqs.map(_.size)
    val max = sizes.product

    val result = new ArrayBuffer[Tuple[T]](max)
    var i = 0

    while (i < max) {
      var c = i
      var sel = -1
      val elem = for (s <- sizes) yield {
        val index = c % s
        c = c / s
        sel += 1
        seqs(sel)(index)
      }

      i+=1
      result += elem
    }

    result
  }
}
