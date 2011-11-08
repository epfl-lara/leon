import org.scalacheck._
import Gen._
import Arbitrary.arbitrary

object Specs {
  sealed abstract class Color
  case class Red() extends Color
  case class Black() extends Color
 
  sealed abstract class Tree
  case class Empty() extends Tree
  case class Node(color: Color, left: Tree, value: Int, right: Tree) extends Tree

  sealed abstract class OptionInt
  case class SomeInt(v : Int) extends OptionInt
  case class NoneInt() extends OptionInt

  def max(a: Int, b: Int) : Int = {
    if (a >= b) a else b
  } ensuring (res => res >= a && res >= b)

  def size(t: Tree) : Int = (t match {
    case Empty() => 0
    case Node(_, l, v, r) => size(l) + 1 + size(r)
  }) ensuring (_ >= 0)

  def height(t: Tree) : Int = (t match {
    case Empty() => 0
    case Node(_,l,_,r) => max(height(l), height(r)) + 1
  }) ensuring (_ >= 0)

  def isBlack(t: Tree) : Boolean = t match {
    case Empty() => true
    case Node(Black(),_,_,_) => true
    case _ => false
  }

  def redNodesHaveBlackChildren(t: Tree) : Boolean = t match {
    case Empty() => true
    case Node(Black(), l, _, r) => redNodesHaveBlackChildren(l) && redNodesHaveBlackChildren(r)
    case Node(Red(), l, _, r) => isBlack(l) && isBlack(r) && redNodesHaveBlackChildren(l) && redNodesHaveBlackChildren(r)
  }

  def blackBalanced(t : Tree) : Boolean = t match {
    case Node(_,l,_,r) => blackBalanced(l) && blackBalanced(r) && blackHeight(l) == blackHeight(r)
    case Empty() => true
  }

  def blackHeight(t : Tree) : Int = t match {
    case Empty() => 0
    case Node(Black(), l, _, _) => blackHeight(l) + 1
    case Node(Red(), l, _, _) => blackHeight(l)
  }

  def valuesWithin(t : Tree, bound : Int) : Boolean = t match {
    case Empty() => true
    case Node(_,l,v,r) => 0 <= v && v <= bound && valuesWithin(l,bound) && valuesWithin(r,bound)
  }

  def orderedKeys(t : Tree) : Boolean = orderedKeys(t, NoneInt(), NoneInt())

  def orderedKeys(t : Tree, min : OptionInt, max : OptionInt) : Boolean = t match {
    case Empty() => true
    case Node(c,a,v,b) =>
      val minOK = 
        min match {
          case SomeInt(minVal) =>
            v > minVal
          case NoneInt() => true
        }
      val maxOK =
        max match {
          case SomeInt(maxVal) =>
            v < maxVal
          case NoneInt() => true
        }
      minOK && maxOK && orderedKeys(a, min, SomeInt(v)) && orderedKeys(b, SomeInt(v), max)
  }

  def isRedBlackTree(t : Tree) : Boolean = {
    blackBalanced(t) && redNodesHaveBlackChildren(t) && orderedKeys(t) // && isBlack(t)
  }
}
object RedBlackTree {
  import Specs._

  val genLeaf = value(Empty())

  def genColor: Gen[Color] = oneOf(Black(), Red())

  val genNode = for {
    v <- Gen.choose(1, 10)
    left <- genTree
    right <- genTree
    color <- genColor
  } yield Node(color, left, v, right)

  def genTree: Gen[Tree] = oneOf(genLeaf, genNode)

  def main(args: Array[String]): Unit = {
    val iter = (new Iterator[Tree] {
      private var counter = 0
      def hasNext : Boolean = true || counter < 10
      def next : Tree = { counter += 1; genTree.sample.get }
    })

    val s = scala.collection.mutable.Set[Int]()

    for (t <- iter if isRedBlackTree(t)) {
      //println("Here is a tree : " + t)
      s += (size(t))
      println(s)
    }
  }
}
