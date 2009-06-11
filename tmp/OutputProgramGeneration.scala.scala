// injected
import org.scalacheck.{Arbitrary,Gen,Prop,Shrink}

//removed
// import funcheck.lib.Specs._

object BSTTest {
  
  def main(args: Array[String]) = {
    println(genBST.sample) 
  }
  
  /** Specification Variables */
  def content(t : BST) : Set[Int] = t match {
    case Leaf() => Set.empty
    case Node(left,right,v) => (content(left) ++ Set(v) ++ content(right))
  }
  
  def contains(key: Int, t : BST): Boolean = { 
    t match {
      case Leaf() => false
      case Node(left,right,v) => {
	    if (key == v) true
	    else if (key < v) contains(key, left)
	    else contains(key, right)
      }
    }
  }
  
  /** Properties */
  // removed
  //val treeContainsValue = forAll[(BST,Int)]( p => contains(p._2,p._1) == content(p._1).contains(p._2))
  
  // injected
  // replaced with ScalaCheck forAll
  val treeContainsValue = Prop.forAll( (tree:BST,v:Int) => contains(v,tree) == content(tree).contains(v))(b: Boolean => Prop.propBoolean(b), arbBST, Shrink.shrinkAny[BST], Arbitrary.arbInt, Shrink.shrinkInt)
  
  /** Program */
  abstract class BST
  case class Node(left: BST, right: BST, v: Int) extends BST
  case class Leaf() extends BST
  
  /**********************************************/
  /**********************************************/
  
  /** Automatically Injected Code*/
  // Generators
  def genBST: Gen[BST] = Gen.lzy(Gen.oneOf(genLeaf,genNode))
  
  val genNode: Gen[Node] = for {
    left <- genBST
    right <- genBST
    v <- Arbitrary.arbitrary[Int]
  } yield Node(left,right,v)
  
  val genLeaf: Gen[Leaf] = Gen.value(Leaf())
  
  // Arbitrary
  def arbBST: Arbitrary[BST] = Arbitrary(genBST)
  def arbNode: Arbitrary[Node] = Arbitrary(genNode)
  def arbLeaf: Arbitrary[Leaf] = Arbitrary(genLeaf)
  
}
