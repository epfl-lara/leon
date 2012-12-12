package examples

object SynthesisExamples {
  var allExamples = List[Example]()

  def newExample(title: String, code: String) {
    allExamples = allExamples ::: Example(title, "synthesis", code) :: Nil
  }

  newExample("ADT Induction", """
import scala.collection.immutable.Set
import leon.Annotations._
import leon.Utils._

object SortedList {
  sealed abstract class List
  case class Cons(head: Int, tail: List) extends List
  case class Nil() extends List

  // proved with unrolling=0
  def size(l: List) : Int = (l match {
      case Nil() => 0
      case Cons(_, t) => 1 + size(t)
  }) ensuring(res => res >= 0)

  //def sizeSynth(l: List): Int = choose{ (i: Int) => i >= 0 && sizeSynth(Cons(0, l)) == i + 1}

  def content(l: List): Set[Int] = l match {
    case Nil() => Set.empty[Int]
    case Cons(i, t) => Set(i) ++ content(t)
  }

  //def artifialSubcase(v : Int) = choose {
  //  (out : List) =>
  //    content(out) == (content(Nil()) -- Set(v))
  //}

  def deleteSynth(in: List, v: Int) = choose {
    (out: List) =>
      // This spec is too weak. Maybe use later as bad example?
      //!(content(out) contains v) && size(out)+1 >= size(in)
      (content(out) == (content(in) -- Set(v)))
  }

  def concatSynth(in1: List, in2: List) = choose {
    (out : List) =>
      content(out) == content(in1) ++ content(in2)
  }

  def isSorted(l: List): Boolean = l match {
    case Nil() => true
    case Cons(x, Nil()) => true
    case Cons(x, Cons(y, ys)) => x <= y && isSorted(Cons(y, ys))
  }
}""".trim)

  newExample("Binary Tree", """
import scala.collection.immutable.Set
import leon.Annotations._
import leon.Utils._

object BinaryTree {
  sealed abstract class Tree
  case class Node(left : Tree, value : Int, right : Tree) extends Tree
  case class Leaf() extends Tree

  def content(t : Tree): Set[Int] = t match {
    case Leaf() => Set.empty[Int]
    case Node(l, v, r) => content(l) ++ Set(v) ++ content(r)
  }

  def delete(in : Tree, v : Int) = choose { (out : Tree) =>
    content(out) == (content(in) -- Set(v))
  }
}
  """.trim)

  newExample("Seconds to Time", """
import leon.Utils._

object Sec2Time {

  def s2t(total: Int) : (Int, Int, Int) = choose((h: Int, m: Int, s: Int) => 3600*h + 60*m + s == total && h >= 0 && m >= 0 && m < 60 && s >= 0 && s < 60)

}
  """.trim)
}
