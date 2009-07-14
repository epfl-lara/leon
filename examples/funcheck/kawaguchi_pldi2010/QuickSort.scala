package funcheck.kawaguchi_pldi2010

/* Example from paper "Type-based Data Structure Verification"
 * http://pho.ucsd.edu/liquid/demo/index2.php */

import funcheck.lib.Specs._

object QuickSort {

  sealed abstract class Top(v: Int)
  case class T(v: Int) extends Top(v)
  case class F(v: Int) extends Top(v)
  
  def partition(f: Int => Top, xs: List[Int]): (List[Int],List[Int]) = xs match {
    case Nil => (Nil,Nil)
    case x :: xs => 
      val (ts,fs) = partition(f, xs)
      f(x) match {
        case T(x) => (x :: ts, fs)
        case F(x) => (ts, x :: fs)
      }
  }
  
  
  def quicksort(xs: List[Int]): List[Int] = xs match {
    case Nil => Nil
    case x :: xs => 
      val (ls,rs) = partition(y => if (y < x) T(y) else F(x), xs)
      val ls1 = quicksort(ls)
      val rs1 = quicksort(rs)
      ls1 ::: (x :: rs1)
  }
  
  def check(xs: List[Int]): Boolean = xs match {
    case Nil => true
    case List(x) => true
    case x :: y :: xs => 
      (x <= y) && check(y :: xs)
  }
  
  def test(xs: List[Int]): Boolean = check(quicksort(xs))
  
  forAll{xs: List[Int] => test(xs)}
  
  def main(args: Array[String]) = {}
}
