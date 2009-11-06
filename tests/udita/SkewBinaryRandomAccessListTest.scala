package udita

import scala.collection.immutable.Multiset;
import gov.nasa.jpf.jvm.Verify;

object SkewBinaryRandomAccessListTest extends Application {

  sealed abstract class Tree
  case class Leaf(w: Int) extends Tree
  case class Node(w: Int, left: Tree, right: Tree) extends Tree
  
  type RList = List[(Int, Tree)]  
  
  val empty = Nil
  
  def isEmpty(ts: RList) = ts.isEmpty
  
  def cons(w: Int, ts: RList): RList = ts match {
    case (w1,t1) :: (w2,t2) :: rest if (w1 == w2) => 
      (1+w1+w2, Node(w,t1,t2)) :: rest
      
    case _ => 
      (1, Leaf(w)) :: ts 
  }
  
  def head(ts: RList): Int = ts match {
    case Nil => error("head of empty list")
    case (1, Leaf(x)) :: ts => x
    case (_, Node(x, _, _)) :: ts => x
  }
  
  def tail(ts: RList): RList = ts match {
    case Nil => error("tail of empty list")
    case (1, Leaf(x)) :: ts => ts
    case (w, Node(x, t1, t2)) :: rest => 
      (w/2, t1) :: (w/2, t2) :: rest
  }
  
  def lookup(i: Int, ts: RList): Int = ts match {
    case Nil => error("lookup of empty list")
    case (w,t) :: ts =>
      if (i < w) lookupTree(w,i,t)
      else lookup(i-w, ts)
  }
  
  def lookupTree(w: Int, i: Int, t: Tree): Int = (w,i,t) match {
    case (1,0, Leaf(x)) => x
    case tuple @ (1,_,Leaf(x)) => error("lookupTree: error for "+tuple)
    case (_,0, Node(x,_,_)) => x
    case (_,_,Node(x,t1,t2)) =>
      if (i < w/2) lookupTree(w/2,i-1,t1)
      else lookupTree(w/2,i-1-w/2,t2)
  }
  
  def updateTree(w: Int, i: Int, y: Int, t: Tree): Tree = (w,i,y,t) match {
    case (1,0,_,Leaf(x)) => Leaf(y)
    case tuple @ (1,_,_,Leaf(x)) => error("updateTree: Error for "+tuple)
    case (_,0,_,Node(x,t1,t2)) => Node(y,t1,t2)
    case (_,_,_,Node(x,t1,t2)) => 
      if (i <= w/2) Node(x,updateTree(w/2,i-1,y,t1),t2)
      else Node(x,t1, updateTree(w/2,i-1-w/2,y,t2))
  } 
 
  
  def update(i: Int, y: Int, ts: RList): RList = ts match {
    case Nil => error("update of empty list")
    case (w,t) :: ts =>
      if (i < w) (w, updateTree(w,i,y,t)) :: ts
      else (w,t) :: update(i-w,y,ts)
  }
  
  def incTreeList(ws:List[Int]):List[Int] = ws match {
    case w1::w2::rest => {
      if (w1 == w2) (1+w1+w2)::rest;
      else 1 :: ws;
    }
    case _ => 1 :: ws;
  }
  
  def makeSizeList(size:Int):List[Int] = {
    var list:List[Int] = Nil;
    for(i <- 0 until size) {
      list = incTreeList(list);
    }
    return list;
  }
  
  def generateSkewBinaryList(maxSize:Int): RList = {
    val size = Verify.getInt(1, maxSize);
    val sizeList = makeSizeList(size);
    val rl = generateAllTrees(sizeList);
    System.out.println(rl);
    return rl;
  }
  
  def generateAllTrees(sizeList:List[Int]):RList = sizeList match {
    case hd::rest =>  List((hd, generateTree(hd))):::generateAllTrees(rest);
    case Nil => Nil;
  }
    
  private def generateTree(size:Int): Tree = {
    val maxNodeValue = size - 1;
    val t = getSubTree(size, 0, 0);//should go up to maxNodeValue
    //System.out.println(t);
    return t;
  }
  
  private def getSubTree(size:Int, min:Int, max:Int): Tree = {
    if (size == 1) return Leaf(Verify.getInt(min,max));
    val value = Verify.getInt(min,max);
    val subtreeSize = (size-1) / 2;
    return Node(value, getSubTree(subtreeSize, min, max), getSubTree(subtreeSize, min, max));
  }

  def content(t : RList): Multiset[Int] = {
    def inner(t: Tree, mset: Multiset[Int]): Multiset[Int] = t match {
      case Leaf(value) => mset +++ List(value);
      case Node(value, left, right) => inner(right,inner(left, mset +++ List(value)));
    }
    def innerList(ts: RList, mset:Multiset[Int]): Multiset[Int] = ts match {
      case Nil => mset
      case (w,t)::tss => inner(t, innerList(tss,mset))
    }   
    innerList(t,Multiset.empty[Int]);
  }
  
    
  //generateSkewBinaryList(4);
  
  def forAll(property : ((RList,Int) => Boolean)){
    assert(property(generateSkewBinaryList(4), 4));//Verify.getInt(0,4)));
  }

  forAll((skew, value) => (content(cons(value,skew)) == content(skew) +++ List(value)));

}
