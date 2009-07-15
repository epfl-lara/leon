package plugin

import funcheck.lib.Specs._

/* SkewBinaryRandomAccessList: Okasaki's "Purely Functional Data Structures" p.134 Fig. 9.7. */

object SkewBinaryRandomAccessList {

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
  
  def main(args: Array[String]): Unit = {}
}
