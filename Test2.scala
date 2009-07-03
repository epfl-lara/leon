import funcheck.lib.Specs._
import org.scalacheck.{Gen, Arbitrary}

object HeapTest {
  @generator
  sealed abstract class Tree 
  case class Leaf()  extends Tree
  case class Node(left: Tree, right: Tree, v:Int) extends Tree

  @generator def create(left: Tree, right: Tree, v: Int): Node = Node(left,right,v)

  case class Elem (i: Int, j: Int, k: Int)
  
  def genElem: Gen[Elem] = for {
    i <- Arbitrary.arbitrary[Int]
    j <- Arbitrary.arbitrary[Int]
    k <- Arbitrary.arbitrary[Int]
  } yield Elem(i,j,k)
 
  def genLeaf = Gen.value(Leaf())
  def genTree: Gen[Tree] = Gen.oneOf(genLeaf,genNode)
  def genNode = for {
    v1 <- Arbitrary.arbitrary[Tree]
    v2 <- Arbitrary.arbitrary[Tree]
    v3 <- Arbitrary.arbitrary[Int]
  } yield Node(v1,v2,v3)

  implicit def arbTree: Arbitrary[Tree] = Arbitrary(genTree)

  
}