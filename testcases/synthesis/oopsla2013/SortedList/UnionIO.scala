import leon.annotation._
import leon.lang._
import leon.lang.synthesis._

object Complete {
  sealed abstract class List
  case class Cons(head: Int, tail: List) extends List
  case object Nil extends List

  def size(l: List) : Int = (l match {
      case Nil => 0
      case Cons(_, t) => 1 + size(t)
  }) ensuring(res => res >= 0)

  def content(l: List): Set[Int] = l match {
    case Nil => Set.empty[Int]
    case Cons(i, t) => Set(i) ++ content(t)
  }

  def isSorted(list : List) : Boolean = list match {
    case Nil => true
    case Cons(_, Nil) => true
    case Cons(x1, Cons(x2, _)) if(x1 > x2) => false
    case Cons(_, xs) => isSorted(xs)
  }

  // def union(in1: List, in2: List): List = {
  //   require(isSorted(in1) && isSorted(in2))
  //   in1 match {
  //     case Cons(h1, t1) =>
  //       union(t1, insert(in2, h1))
  //     case Nil =>
  //       in2
  //   }
  // } ensuring { res => content(res) == content(in1) ++ content(in2) && isSorted(res) }

/*
  def union(in1: List, in2: List) = choose {
    (out : List) =>
      isSorted(in1) && isSorted(in2) && (content(out) == content(in1) ++ content(in2)) && isSorted(out)
  }
*/

  def union(in1: List, in2: List) = {
    require(isSorted(in1) && isSorted(in2))
    choose { (out : List) =>
       (in1!= Cons(10,Cons(20,Cons(30,Cons(40,Nil)))) || 
        in2!= Cons(11,Cons(13,Cons(25,Cons(45,Cons(48,Cons(60,Nil)))))) || 
        out == Cons(10,Cons(11,Cons(13,Cons(20,Cons(25,Cons(30,Cons(40,Cons(45,Cons(48,Cons(60,Nil))))))))))) &&
       (content(out) == content(in1) ++ content(in2)) && isSorted(out) }
  }
}
