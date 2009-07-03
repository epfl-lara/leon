import scala.collection.immutable.Set
import funcheck.Specs.{`==>`,forAll}

object ListSet {
  $\forall$ x: Int, xs: List[Int] .
    content(insert(x, xs)) = content(xs) + x

  $\forall$ x: Int, xs: List[Int] .
    content(delete(x, xs)) = content(xs) - x

  $\forall$ xs: List[Int], ys: List[Int], z: Int .
    content(xs) == content(ys) ==> content(insert(z, xs)) == content(insert(z, ys))

  $\forall$ xs: List[Int], ys: List[Int], z: Int .
    content(xs) == content(ys) ==> content(delete(z, xs)) == content(delete(z, ys))

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
