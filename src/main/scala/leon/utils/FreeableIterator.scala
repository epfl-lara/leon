package leon
package utils

abstract class FreeableIterator[T] extends Iterator[T] {
  private[this] var nextElem: Option[T] = None

  def hasNext = {
    nextElem = computeNext()
    nextElem.nonEmpty
  }

  def next() = {
    nextElem.get
  }

  def computeNext(): Option[T]

  def free()
}
