import scala.collection.immutable.Set

object ListSet {
  def content(xs: List[Int]): Set[Int] = xs match {
    case Nil => Set.empty
    case x :: xs => content(xs) + x
  }

  def insert(x: Int, xs: List[Int]): List[Int] = if(member(x, xs)) xs else insert(x, xs)

  def remove(x: Int, xs: List[Int]): List[Int] = xs match {
    case Nil => Nil
    case y :: ys if y == x => remove(x, ys)
    case y :: ys if y != x => y :: remove(x, ys)
  }

  def member(x: Int, xs: List[Int]): Boolean = xs match {
    case Nil => false
    case y :: _ if y == x => true
    case _ :: ys => member(x, ys)
  }

  def main(args: Array[String]): Unit = {
    val l1: List[Int] = List(1, 2, 3, 4)
    val l2: List[Int] = List(2, 3, 3, 4, 1)

    println(content(l1) == content(l2)) // true
    println(content(insert(5, l1)) == content(insert(5, l2))) // true
    println(content(insert2(3, l1)) == content(insert2(3, l2))) // true
  }
}
