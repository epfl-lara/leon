package contracts.insertionsort

import scala.collection.immutable.Set

object InsertionSort {
  import funcheck.lib.Specs

  assert(
    Specs.forAll(
      (l: List[Int]) => { content(sorted(l)) equals content(l) }
    )
  )

  def content(l: List[Int]): Set[Int] = l match {
    case Nil => Set.empty
    case x :: xs => content(xs) + x
  }

  def sortedIns(e: Int, l: List[Int]): List[Int] = l match {
    case Nil => e :: Nil
    case x :: xs if (x < e) => x :: sortedIns(e, xs)
    case _ => e :: l
  }

  def sorted(l: List[Int]): List[Int] = l match {
    case Nil => Nil
    case x :: xs => sortedIns(x, sorted(xs))
  }

  def main(args: Array[String]): Unit = {
    val ls: List[Int] = List(5, 2, 4, 5, 1, 8)

    println(ls)
    println(sorted(ls))
  }
}
