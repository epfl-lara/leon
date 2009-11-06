package udita

import scala.collection.immutable.Multiset;
import gov.nasa.jpf.jvm.Verify;

object BinomialHeapTest extends Application {
  sealed case class BinomialHeap(trees:List[BinomialTree]);
  
  sealed case class BinomialTree(rank:Int, value:Int, children:List[BinomialTree]);
  
  def rankk(t1:BinomialTree):Int = t1 match {
    case BinomialTree(rank, _, _) => rank;
  }
  
  def root(t1:BinomialTree):Int = t1 match {
    case BinomialTree(_, value, _) => value;
  }
  
  def link(t1:BinomialTree, t2:BinomialTree):BinomialTree = t1 match {
    case BinomialTree(rank1,value1,children1) => t2 match {
      case BinomialTree(rank2,value2,children2) => {
        if (value1 <= value2) BinomialTree(rank1+1, value1, t2::children1); 
        else BinomialTree(rank2+1, value2, t1::children2);
      }
    }
  }
  
  def insertTree(t:BinomialTree, trees:List[BinomialTree]):List[BinomialTree] = trees match {
    case Nil => List(t);
    case t1::ts1 => {
      if (rankk(t) < rankk(t1)) t::trees;  //bug t::ts1;
      else insertTree(link(t,t1),ts1);
    }
  }
  
  def insert(x:Int, trees:List[BinomialTree]):List[BinomialTree] = insertTree(BinomialTree(0,x,Nil), trees);
  
  def insert(x:Int, heap:BinomialHeap):BinomialHeap = heap match {
    case BinomialHeap(ts) => BinomialHeap(insert(x,ts));
  }                                                                             
  
  def merge(ts1:List[BinomialTree],ts2:List[BinomialTree]):List[BinomialTree] = ts1 match {
    case Nil => ts2;
    case t1::tss1 => ts2 match {
      case Nil => ts1;
      case t2::tss2 => {
        if (rankk(t1) < rankk(t2)) t1::merge(tss1,ts2);
        else if (rankk(t2) < rankk(t1)) t2::merge(ts1,tss2);
        else insertTree(link(t1,t2),merge(tss1,tss2)); 
      }
    }
  }
  
  def removeMinTree(ts:List[BinomialTree]):(BinomialTree,List[BinomialTree]) = ts match {
    case t1::Nil => (t1,Nil);
    case t1::ts1 => {
      val (t11,ts11) = removeMinTree(ts1);
      if (root(t1) <= root(t11)) (t1,ts1);
      else (t11,t1::ts11);
    }
    case Nil => error("removing from empt tree");
  }
  
  def findMin(ts:List[BinomialTree]):Int = {
    val (t1,_) = removeMinTree(ts);
    root(t1);
  }
  
  def deleteMin(ts:List[BinomialTree]):List[BinomialTree] ={
    val (BinomialTree(_,x,ts1),ts2) = removeMinTree(ts);
    merge(ts1.reverse,ts2);
  }
  
  def deleteMin(heap:BinomialHeap):BinomialHeap = heap match {
    case BinomialHeap(ts) => BinomialHeap(deleteMin(ts));
  }
  
  def findMin(heap:BinomialHeap):Int = heap match {
    case BinomialHeap(ts) => findMin(ts);
  }
  
  def generateBinomialTree(rank:Int, min:Int, max:Int): BinomialTree = {
    if(rank == 0) BinomialTree(rank, Verify.getInt(min,max), Nil);
    else {
      val value = Verify.getInt(min,max - rank);
      var list = List[BinomialTree]();
      for(i <- 0 until rank) {
        list = generateBinomialTree(i,value+1,max)::list;
      }
      BinomialTree(rank,value,list);
    }
  }
  
  def generateBinomialHeap(heapSize:Int):BinomialHeap = {
   var div:Int = heapSize;
   var list = List[BinomialTree]();
   var i = 0;
   while(div > 0) {
     var mod:Int = div % 2;
     if (mod == 1) {
       list= list ::: List(generateBinomialTree(i,0,heapSize));
     }
     div = div/2;
     i+=1;
   }
   BinomialHeap(list);
  }

  def content(t : BinomialHeap): Multiset[Int] = {
     def inner(t: BinomialTree, mset: Multiset[Int]): Multiset[Int] = t match {
      case BinomialTree(rank, value, children) => {
        innerList(children, mset +++ List(value));
      }
     }
     def innerList(ts: List[BinomialTree], mset:Multiset[Int]): Multiset[Int] = ts match {
       case Nil => mset
       case t::tss => inner(t, innerList(tss,mset))
     }
     t match {
       case BinomialHeap(ts) => innerList(ts,Multiset.empty[Int]);
     }
  }
  
  
  var heap = BinomialHeap(Nil);
  heap = insert(5,insert(26,insert(1,insert(17,insert(4,heap)))));
  
//  System.out.println(heap);
//  System.out.println(findMin(heap));
//  System.out.println(deleteMin(heap));
//  System.out.println(content(heap));
//  
//  System.out.println(content(insert(1,heap)) == content(heap) +++ List(1));
//  System.out.println(generateBinomialHeap(3));
// 
                                            
  def forAll(property : ((BinomialHeap,Int) => Boolean)){
    assert(property(generateBinomialHeap(4), Verify.getInt(0,4)));
  }

  forAll((heap, value) => (content(insert(value,heap)) == content(heap) +++ List(value)));

}
