import leon.invariant._
import leon.instrumentation._

object TreeOperations {

  sealed abstract class Tree
  case class Node(left: Tree, value: BigInt, right: Tree) extends Tree
  case class Leaf() extends Tree

  def size(t: Tree): BigInt = {
    t match {
      case Leaf() => BigInt(0)
      case Node(l, x, r) => {
        size(l) + size(r) + 1
      }
    }
  } //ensuring(_ => steps <= 10)

  def height(t: Tree): BigInt = {
    t match {
      case Leaf() => BigInt(0)
      case Node(l, x, r) => {
        val hl = height(l)
        val hr = height(r)
        if (hl > hr) hl + 1 else hr + 1
      }
    }
  } ensuring(res => steps  <= ? * steps(size(t)) + ?)
}