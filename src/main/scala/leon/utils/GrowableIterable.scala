package leon.utils

import scala.collection.mutable.ArrayBuffer

class GrowableIterable[T](init: Seq[T], growth: Iterator[T]) extends Iterable[T] {
  private val buffer = new ArrayBuffer[T]() ++ init

  def +=(more: T) = buffer += more
  def ++=(more: Seq[T]) = buffer ++= more

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
    buffer.sortBy(f)
  }
}
