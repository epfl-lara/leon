package plugin.kawaguchi

import funcheck.lib.Specs._

/* Example from paper "Type-based Data Structure Verification"
 * http://pho.ucsd.edu/liquid/demo/index2.php */

object MergeSort {

  def halve(xs: List[Int]): (List[Int],List[Int]) = xs match {
    case Nil => (Nil,Nil)
    case x :: xs => 
      val (ys,zs) = halve(xs)
      (x :: zs, ys)
  } 
  
  def merge(xs: List[Int], ys: List[Int]): List[Int] = (xs,ys) match {
    case (Nil,_) => ys
    case (_,Nil) => xs
    case (x :: xs, y :: ys) => 
      if (x < y) x :: merge(xs, y :: ys)
      else y :: merge(x:: xs, ys)
  }
  
  def mergesort(ps: List[Int]): List[Int] = ps match {
    case Nil => Nil
    case List(p) => List(p)
    case _ => 
      val (qs,rs) = halve(ps)
      val qs1 = mergesort(qs)
      val rs1 = mergesort(rs)
      merge(qs1,rs1)
  }
  
  def check(xs: List[Int]): Boolean = xs match {
    case x :: y :: xs => 
      x <= y && check(y :: xs)
      
    case _ => true
  }
  
  def test(xs: List[Int]): Boolean = check(mergesort(xs))
  
  forAll{xs: List[Int] => test(xs)}
  
  def main(args: Array[String]) = {}
}
