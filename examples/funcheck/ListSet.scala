package funcheck

import scala.collection.immutable.Set
import funcheck.lib.Specs._

object ListSet {
  forAll[(Int,List[Int])] (p =>
    content(insert(p._1, p._2)) == content(p._2) + p._1)

  forAll[(Int,List[Int])] (p =>
    content(remove(p._1, p._2)) == content(p._2) - p._1)

  forAll[(List[Int],List[Int],Int)] (p =>
    eqlists(p._1, p._2) ==> eqlists(insert(p._3, p._1), insert(p._3, p._2)))

  forAll[(List[Int],List[Int],Int)] (p =>
    eqlists(p._1, p._2) ==> eqlists(remove(p._3, p._1), remove(p._3, p._2)))

  def eqlists(xs: List[Int], ys: List[Int]): Boolean = content(xs) == content(ys)

  def content(xs: List[Int]): Set[Int] = xs match {
    case Nil => Set.empty
    case x :: xs => content(xs) + x
  }

  //@generator 
  def insert(x: Int, xs: List[Int]): List[Int] = if(member(x, xs)) xs else x :: xs

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

  //@generator 
  def makeNil: List[Int] = Nil
  
  
  def main(args: Array[String]): Unit = {}
}
