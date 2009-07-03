import funcheck.lib.Specs._
import org.scalacheck.{Gen, Arbitrary}

object HeapTest {

  @generator sealed abstract class Tree 
  case class Node(left: Tree, right: Tree) extends Tree
  case class Leaf() extends Tree

  def genLeaf: Gen[Leaf] = Gen.value[Leaf](Leaf())

  def genNode: Gen[Node] = for {
    v1 <- Arbitrary.arbitrary[Tree]
    v2 <- Arbitrary.arbitrary[Tree]
  } yield Node(v1,v2)

  implicit def arbTree: Arbitrary[Tree] = Arbitrary(genTree)
  def genTree: Gen[Tree] = Gen.oneOf(genLeaf,genNode)
  
}