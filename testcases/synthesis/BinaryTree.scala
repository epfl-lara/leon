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
