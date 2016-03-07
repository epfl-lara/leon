package leon.utils

import scala.collection.mutable.ArrayBuffer

class GrowableIterable[T](init: Seq[T], growth: Iterator[T]) extends Iterable[T] {
  var buffer = new ArrayBuffer[T]() ++ init

  val cachingIterator = new Iterator[T] {
    def hasNext = growth.hasNext

    def next() = {
      val res = growth.next()
      buffer += res
      res
    }
  }

  def iterator: Iterator[T] = {
    buffer.iterator ++ cachingIterator
  }

  def sortBufferBy[B](f: T => B)(implicit ord: math.Ordering[B]) = {
    buffer = buffer.sortBy(f)
  }
}
