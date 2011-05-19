import cp.Definitions._
import cp.Terms._

import org.scalacheck._
import Gen._
import Arbitrary.arbitrary

@spec object Specs {
  sealed abstract class Tree
  case class Node(left: Tree, right: Tree, v: Int) extends Tree
  case class Leaf() extends Tree
}
object UserDefinedSolver {
  import Specs._

  val genLeaf = value(Leaf())

  val genNode = for {
    v <- Gen.choose(1, 10)
    left <- genTree
    right <- genTree
  } yield Node(left, right, v)

  def genTree: Gen[Tree] = oneOf(genLeaf, genNode)

  def main(args: Array[String]): Unit = {
    val generator = ((t: Tree) => t != Leaf()).customize(new Iterator[Tree] {
      private var counter = 0
      def hasNext : Boolean = { counter += 1; counter < 10 }
      def next : Tree = genTree.sample.get
    })

    for (t <- generator.findAll) {
      println("Here is a tree : " + t)
    }
  }
}
