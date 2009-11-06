package udita


import scala.collection.immutable.Multiset;
import gov.nasa.jpf.jvm.Verify;

object LeftistHeapTest extends Application {

  sealed abstract class Heap{
    def rankk():Int = this match {
      case Empty => 0;
      case Node(rank,_,_,_) => rank;
    }
    
    def insert(x: Int): Heap = {
      LeftistHeapTest.merge(this, Node(1,x,Empty,Empty))
    }
    
    def findMin(): Int = this match {
      case Empty => Predef.error(toString());
      case Node(_,x,_,_) => x
    }
    
//    override def toString(): String = this match {
//      case Empty => "Empty";
//      case Node(rank,x,left,right) => "Node("+rank+","+x+","+left+","+right+")";
//    }
    
    //ensuring(res => res == min(content(this).elements.toList))
    
    def deleteMin(): Heap = this match {
      case Empty => Predef.error(toString());
      case Node(_, _, left: Heap, right: Heap) => LeftistHeapTest.merge(left,right);
    } 
    //ensuring(res  => content(res).equals(content(this) - findMin))
  }
  
  case class Node(rank:Int, value:Int, left:Heap, right:Heap) extends Heap;
  case object Empty extends Heap;
  
  def merge(heap1:Heap, heap2:Heap): Heap = heap1 match {
    case Empty => heap2;
    case Node(_, value1, left1, right1) => heap2 match {
      case Empty => heap1;
      case Node(_, value2, left2, right2) if (value1 <= value2) =>
        makeAndSwap(left1, value1, merge(right1,heap2));
      case Node(_, value2, left2, right2) if (value1 > value2) =>
        makeAndSwap(left2, value2, merge(heap1,right2));
    }
  }
  
  def makeAndSwap(left:Heap, value:Int, right:Heap): Heap = {
    if(left.rankk() >= right.rankk()){
      Node(right.rankk() + 1, value, left, right);
    } else {
      Node(left.rankk() + 1, value, right, left);      
    }
  }
  
  
  def forAllLeftistHeap(size:Int, property:(Heap=>Boolean)): Boolean = {
    property(generateLeftistHeap(size));
  }
  
  def generateLeftistHeap(treeSize:Int):Heap = {
    val size = Verify.getInt(1, treeSize);
    val maxNodeValue = size - 1;
    val t = getSubTree(size, -1, maxNodeValue - 1);
    System.out.println(t);
    return t;
  }
  
  private def getSubTree(size:Int, min:Int, max:Int): Heap = {
    if (size == 0) return Empty;
    if (size == 1) return Node(1, Verify.getInt(min+1,max+1), Empty, Empty);

    val value = Verify.getInt(min+1,max+1);
    val rightSize = Verify.getInt(0,(size - 1)/2);
    val leftSize = size - 1 - rightSize;
    
    val rightSub = getSubTree(rightSize, value, max);
    val leftSub = getSubTree(leftSize, value, max);
    
    return Node(rightSub.rankk() + 1, value, leftSub, rightSub);
  }
  
  def content(t : Heap): Multiset[Int] = {
    def inner(t: Heap, mset: Multiset[Int]): Multiset[Int] = t match {
      case Empty => mset
      case Node(rank,value,left,right) => inner(right, inner(left, mset +++ List(value)))
    }
    inner(t,Multiset.empty[Int]);
  }
  
  def forAll(property : ((Heap,Int) => Boolean)){
    assert(property(generateLeftistHeap(4), 0));//Verify.getInt(0,4)));
  }

  forAll((heap: Heap, value: Int) => content(heap.insert(value)) == content(heap) +++ List(value));

}