import scala.collection.immutable.Set
import funcheck.Specs.forall

object ListSet {
  assert(forall(
    (ls1: List[Int]) => forall(
    (ls2: List[Int] => )

  def content(xs: List[Int]): Set[Int] = xs match {
    case Nil => Set.empty
    case x :: xs => content(xs) + x
  }

  def insert(x: Int, xs: List[Int]): List[Int] = if(member(x, xs)) xs else insert(x, xs)

  def remove(x: Int, xs: List[Int]): List[Int] = xs match {
    case Nil => Nil
    case y :: ys if (y == x) => remove(x, ys)
    case y :: ys if (y != x) => y :: remove(x, ys)
  }

  def member(x: Int, xs: List[Int]): Boolean = xs match {
    case Nil => false
    case y :: _ if (y == x) => true
    case _ :: ys => member(x, ys)
  }

  def main(args: Array[String]): Unit = {
    /* ... */
  }
}
