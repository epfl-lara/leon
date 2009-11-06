package udita

import gov.nasa.jpf.jvm.Verify;

object RedBlackTreeTest extends Application {
  
  val RED:Boolean = true;
  val BLACK:Boolean = false; 
  
  sealed abstract class Tree
  case class Empty() extends Tree
  case class Node(color: Boolean, left: Tree, value: Int, right: Tree) extends Tree
  
  
  def member(x: Int, t:Tree): Boolean = t match {
    case Empty() => false
    case Node(_,a,y,b) => 
      if (x < y) member(x,a)
      else if (x > y) member(x,b)
      else true
  }
  
  def insert(x: Int, t: Tree): Tree = {
    def ins(t: Tree): Tree = t match {
      case Empty() => Node(RED,Empty(),x,Empty())
      case Node(c,a,y,b) =>
        if      (x < y)  balance(c, ins(a), y, b)
        else if (x == y) Node(c,a,y,b)
        else             balance(c,a,y,ins(b))
    }
    makeBlack(ins(t))
  }
  
  def balance(c: Boolean, a: Tree, x: Int, b: Tree): Tree = (c,a,x,b) match {
    case (BLACK,Node(RED,Node(RED,a,xV,b),yV,c),zV,d) => 
      Node(RED,Node(BLACK,a,xV,b),yV,Node(BLACK,c,zV,d))
    case (BLACK,Node(RED,a,xV,Node(RED,b,yV,c)),zV,d) => 
      Node(RED,Node(BLACK,a,xV,b),yV,Node(BLACK,c,zV,d))
    case (BLACK,a,xV,Node(RED,Node(RED,b,yV,c),zV,d)) => 
      Node(RED,Node(BLACK,a,xV,b),yV,Node(BLACK,c,zV,d))
    case (BLACK,a,xV,Node(RED,b,yV,Node(RED,c,zV,d))) => 
      Node(RED,Node(BLACK,a,xV,b),yV,Node(BLACK,c,zV,d))
    case (c,a,xV,b) => Node(c,a,xV,b)
  }
  
  /** makeBLACK: Turn a node BLACK. */
  def makeBlack(n: Tree): Tree = n match {
    case Node(RED,l,v,r) => Node(BLACK,l,v,r)
    case _ => n
  }
  
  /* global invariants: 
   * RED-BLACK trees are binary search trees obeying two key invariants:
   *
   * (1) Any path from a root node to a leaf node contains the same number
   *     of BLACK nodes. (A balancing condition.)
   *
   * (2) RED nodes always have BLACK children.
   *
   */
  
  /* Empty tree are consideRED to be BLACK */
  def isBLACK(t: Tree): Boolean = t match {
    case Node(RED,_,_,_) => false
    case _ => true
  }
  
  
  def anyPathsContainsSameNumberOfBlackNodes(t: Tree): Boolean = {
    def blacks(t: Tree, acc: Int): List[Int] = t match {
      case Empty() => List(acc + 1) // because Empty are assumed to be BLACK
      case Node(_,l,_,r) => 
        val upAcc = if(isBLACK(t)) acc + 1 else acc 
        blacks(l,upAcc) ::: blacks(r,upAcc)  
    }
    val paths = blacks(t, 0)
    
    if(paths.isEmpty)
      true
    else
      paths.forall(_ == paths.head)
  } 
  
  def areRedNodeChildrenBlack(t: Tree): Boolean = t match {
    case Node(RED,l,_,r) =>
      isBLACK(l) && isBLACK(r) &&
      areRedNodeChildrenBlack(l) && areRedNodeChildrenBlack(r)
    case Node(BLACK,l,_,r) =>
      areRedNodeChildrenBlack(l) && areRedNodeChildrenBlack(r)
    case _ => true
  }
  
  def generateRedBlackTree(treeSize:Int): Tree = {
    val t = generateBinarySearchTree(treeSize);
    Verify.ignoreIf(!anyPathsContainsSameNumberOfBlackNodes(t) || !areRedNodeChildrenBlack(t));
    return t;
  }
  
  private def generateBinarySearchTree(treeSize:Int): Tree = {
    val size = Verify.getInt(1, treeSize);
    val maxNodeValue = size - 1;
    val t = getSubTree(size, 0, maxNodeValue);
    return t;
  }
  
  private def getSubTree(size:Int, min:Int, max:Int): Tree = {
    if (size == 0) return Empty();
    if (size == 1) return Node(Verify.getBoolean(), Empty(), Verify.getInt(min,max), Empty());

    val value = Verify.getInt(min,max);

    val leftSize = value - min;
    val rightSize = size - 1 - leftSize;

    return Node(Verify.getBoolean(), getSubTree(leftSize, min, value - 1), value, getSubTree(rightSize, value + 1, max));
  }
  
  def content(t:Tree):Set[Int] = t match {
    case Empty() => Set.empty;
    case Node(_,left,value,right) => (content(left) ++ Set(value) ++ content(right));
  }
  
  def forAll(property: (Tree,Int) => Boolean){     
    val t = generateRedBlackTree(4);
    val x = Verify.getInt(0,4);
    assert(property(t,x));
    System.out.println(x+" "+t);
  }
  
  forAll((t:Tree, x:Int)  => ({val t1 = insert(x,t); anyPathsContainsSameNumberOfBlackNodes(t1) && areRedNodeChildrenBlack(t1)}));
  //forAll{t: Tree => areRedNodeChildrenBlack(t)} //(2)

  //generateRedBlackTree(4);

}
