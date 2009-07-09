package plugin.kawaguchi

/* Example from paper "Type-based Data Structure Verification"
 * http://pho.ucsd.edu/liquid/demo/index2.php */

import funcheck.lib.Specs._

object InsertSort {

  def insert(ys: List[Int], x: Int): List[Int] = ys match {
    case Nil => List(x)
    case y :: ys => 
      if (x < y) x :: y :: ys
      else y :: insert(ys,x)
  }
  
  def insert_sort(xs: List[Int]): List[Int] = xs match {
    case Nil => Nil
    case x :: xs => 
      insert(insert_sort(xs),x)
  }
  
  def insert_sort2(xs: List[Int]): List[Int] = 
    xs.foldLeft[List[Int]](Nil)((x,xs) => insert(x,xs))
  
  def check(xs: List[Int]): Boolean = xs match {
    case Nil => true
    case List(x) => true
    case x :: y :: xs => 
      x <= y && check(y :: xs)
  }
  
  def test(xs: List[Int]): Boolean = 
    check(insert_sort(xs)) && check(insert_sort2(xs))
  
  forAll{xs: List[Int] => test(xs)}
  
  def main(args: Array[String]) = {}
}
