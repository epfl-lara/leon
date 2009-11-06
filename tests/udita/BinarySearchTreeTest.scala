package udita

import gov.nasa.jpf.jvm.Verify;

object BinarySearchTreeTest  extends Application {

  sealed abstract class BinarySearchTree;
  case object Empty extends BinarySearchTree;
  case class Node(left: BinarySearchTree, value:Int, right:BinarySearchTree) extends BinarySearchTree;

  def size(t: BinarySearchTree): Int = t match {
    case Empty => 0;
    case Node(left,value,right) => size(left) + 1 + size(right);
  }
  
  def add(x: Int, t:BinarySearchTree):BinarySearchTree =t match {
    case Empty => Node(Empty,x,Empty);
    case Node(left,value,right) if (x < value) => Node(add(x,left),value,right);
    case Node(left,value,right) if (x >= value) => Node(left,value,add(x,right));    
  }
  
  def contains(x :Int, t:BinarySearchTree):Boolean = t match {
    case Empty => false;
    case Node(left,value,right) if (x == value) => true;
    case Node(left,value,right) if (x < value) => contains(x,left);
    case Node(left,value,right) if (x > value) => contains(x,right);
  }
  
  private def generateBinarySearchTree(treeSize:Int): BinarySearchTree = {
    val size = Verify.getInt(1, treeSize);
    val maxNodeValue = size - 1;
    val t = getSubTree(size, 0, maxNodeValue);
    System.out.println(t);
    return t;
  }
  
  private def getSubTree(size:Int, min:Int, max:Int): BinarySearchTree = {
    if (size == 0) return Empty;
    if (size == 1) return Node(Empty, Verify.getInt(min,max), Empty);

    val value = Verify.getInt(min,max);

    val leftSize = value - min;
    val rightSize = size - 1 - leftSize;

    return Node(getSubTree(leftSize, min, value - 1), value, getSubTree(rightSize, value + 1, max));
  }
  
  def content(t:BinarySearchTree):Set[Int] = t match {
    case Empty => Set.empty;
    case Node(left,value,right) => (content(left) ++ Set(value) ++ content(right));
  }
  
//  def forallTree(treeSize:Int,property : (BinarySearchTree => Boolean)):Boolean = {
//      property(generateBinarySearchTree(treeSize));
//  }
//  
//  def forallInt(min:Int, max:Int, property: (Int => Boolean)) : Boolean ={
//    property(Verify.getInt(min,max));
//  }
  
  //val t = add(17, add(6, add(3, add(5,add(3,Empty)))));
  
  //testing tree
//  System.out.println(t);
//  System.out.println(content(t));
//  System.out.println(size(t));
//  System.out.println(contains(5,t));
  
  //testing getInt
  //assert(forallInt(0,4,(x => forallTree(4,t => content(add(x,t)) == content(t) + x))));
  
  def forAll(property:(BinarySearchTree,Int)=> Boolean){
    assert(property(generateBinarySearchTree(4),Verify.getInt(0,4)));
  }
  
  forAll((t:BinarySearchTree, x:Int) => content(add(x,t)) == content(t) + x);
  
  //System.out.println(generateBinarySearchTree(4));
  //System.out.println("property: "+forallInt(0,4,(x => forallTree(4,t => content(add(x,t)) == content(t) + x))));
}




