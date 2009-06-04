package scalacheck.examples

import org.scalacheck.{Arbitrary,Properties,Gen}
import org.scalacheck.Prop._
import org.scalacheck.ConsoleReporter.testStatsEx
import org.scalacheck.Test.check
import org.scalacheck.Arbitrary.arbitrary

object BSTSpec {
  import contracts.bstdefspec.BSTAsSet._
  
  /**********************************************************/
  /*********************** GENERATORS ***********************/
  /**********************************************************/
  implicit def arbitraryTree: Arbitrary[BST] =
    Arbitrary(smallListInt.map(xs => {
      
      def makeTree(t: BST, xs: List[Int]): BST = xs match {
        case Nil => t
        case x :: xs => makeTree(add(x,t),xs)
      }
                                             
      makeTree(Empty, xs)
    }))

  // gen list (size undefined) of small integer (likely to have duplicates)
  val smallInt = Gen.choose(0,5) 
  val smallListInt = Gen.listOf[Int](smallInt)
  
  
  /**********************************************************/
  /*********************** PROPERTIES ***********************/
  /**********************************************************/
  val treeContainsValue = forAll( (tree: BST, value: Int) => contains(value,tree) == content(tree).contains(value))
  val treeInsertValue   = forAll( (tree: BST, value: Int) => content(add(value, tree)) == content(tree) + value)
  
  
  /**********************************************************/
  // collect tests
  val tests = List(
    ("treeContainsValue",  treeContainsValue),
    ("treeInsertValue", treeInsertValue)
  )
  
  // main
  def main(args: scala.Array[String]) = 
    tests foreach { case (name, p) => testStatsEx(name, check(p)) }
}
