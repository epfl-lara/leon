package udita

import gov.nasa.jpf.jvm.Verify;

object SplayHeapTest extends Application {
  sealed abstract class Heap
  case class E() extends Heap
  case class T(x: Int, a: Heap, b: Heap) extends Heap
  
  def isEmpty(h: Heap): Boolean = h.isInstanceOf[E]
  
  def partition(pivot: Int, t: Heap): (Heap,Heap) = t match {
    case E() => (E(),E())
    case T(x,a,b) =>
      if(x <= pivot) b match {
        case E() => (T(x,a,E()),E())
        case T(y,b1,b2) =>
          if(y <= pivot) {
            val (small,big) = partition(pivot,b2)
            val r1 = T(y,T(x,a,b1),small)
            val r2 = big
            (r1,r2)
          } else  {
            val (small,big) = partition(pivot,b1)
            val r1 = T(x, a, small)
            val r2 = T(y, big, b2)
            (r1,r2)
          }
      } else a match {
        case E() => (E(), T(x,E(),b))
        case T(y,a1,a2) =>
          if(y <= pivot) {
            val (small,big) = partition(pivot,a2)
            val r1 = T(y,a1,small)
            val r2 = T(x,big,b)
            (r1,r2)
          } else {
            val (small,big) = partition(pivot,a1)
            val r1 = small
            val r2 = T(y,big,T(x,a2,b))
            (r1,r2)
          }
      }
  }
  
  def insert(x: Int, t: Heap): Heap = {
    val (a,b) = partition(x,t)
    T(x,a,b)
  }
  
  def merge(t1: Heap, t2: Heap): Heap = t1 match {
    case E() => t2
    case T(x,a,b) =>
      val (ta,tb) = partition(x,t2)
      val a1 = merge(ta,a)
      val b1 = merge(tb,b)
      T(x,a1,b1)
  }
  
  def deleteMin(t: Heap): Heap = t match {
    case E() => error("empty")
    case T(x,E(),b) => b
    case T(y,T(x,E(),b),c) => T(y,b,c)
    case T(y,T(x,a,b),c) => T(x,deleteMin(a),T(y,b,c))  
  }
  
  def deleteMin2(t: Heap): (Int,Heap) = t match {  
    case E() => error("empty")
    case T(x,E(),b) => (x, b)
    case T(y,T(x,E(),b),c) => (x,T(y,b,c))
    case T(y,T(x,a,b),c) =>
      val (r, a1) = deleteMin2(a)
      (r,T(x,a1,T(y,b,c)))
  }
  
  def findMin(t: Heap): Int = t match { 
    case E() => error("empty")
    case T(x,E(),b) => x
    case T(x,a,b) => findMin(a)
  }
  
  def findMin2(t: Heap): (Int,Heap) = t match {
    case E() => error("empty")
    case T(x,E(),b) => (x, t)
    case T(x,a,b) =>
      val (x1, a1) = findMin2(a)
      (x1,T(x,a1,b))
  }
  
  def app(x: Int, ys: List[Int],  zs: List[Int]): List[Int] = ys match {
    case Nil => x :: zs
    case y :: ys => y :: app(x,ys,zs)
  }
  

  def to_list(t: Heap): List[Int] = t match { 
    case E() => Nil
    case T(x,a,b) => app(x,to_list(a),to_list(b))
  }

  def check_sorted(xs: List[Int]): Boolean = xs match {
    case Nil => true
    case x :: xs =>
      xs.forall(x <= _) && check_sorted(xs)
  }

  def to_list2(t: Heap): List[Int] = { 
    val xs = to_list(t)
    check_sorted(xs)
    xs
  }
  
  def generateSplayHeap(treeSize:Int): Heap = {
    return generateBinarySearchTree(treeSize);
  }
  
  private def generateBinarySearchTree(treeSize:Int): Heap = {
    val size = Verify.getInt(1, treeSize);
    val maxNodeValue = size - 1;
    val t = getSubTree(size, 0, maxNodeValue);
    return t;
  }
  
  private def getSubTree(size:Int, min:Int, max:Int): Heap = {
    if (size == 0) return E();
    if (size == 1) return T(Verify.getInt(min,max), E(), E());

    val value = Verify.getInt(min,max);

    val leftSize = value - min;
    val rightSize = size - 1 - leftSize;

    return T(value, getSubTree(leftSize, min, value - 1), getSubTree(rightSize, value + 1, max));
  }
  
  def content(t:Heap):Set[Int] = t match {
    case E() => Set.empty;
    case T(value,left,right) => (content(left) ++ Set(value) ++ content(right));
  }
  
  def forAll(property: (Heap) => Boolean){     
    val t = generateSplayHeap(4);
    assert(property(t));
    System.out.println(t);
  }
  
  forAll{h: Heap => check_sorted(to_list(h))}
}
