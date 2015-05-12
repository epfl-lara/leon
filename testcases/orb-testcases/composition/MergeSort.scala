import leon.invariant._
import leon.instrumentation._
<<<<<<< HEAD

=======
>>>>>>> b03689012b84b65708b49a01c70e68ceb6f413bf
import leon.annotation._

object MergeSort {
  sealed abstract class List
  case class Cons(head:BigInt,tail:List) extends List
  case class Nil() extends List
<<<<<<< HEAD

  @monotonic
  def log(x: BigInt) : BigInt = {
    require(x >= 0)
    if(x <= 1) -1
    else {
      // val k = x/2
      // 1 + log(x - k)
      1 + log(x / 2)
    }
  } ensuring(res => true && res >= -1)

  def size(list:List): BigInt = {list match {
    case Nil() => 0
    case Cons(x,xs) => 1 + size(xs)
  }} ensuring(res => true && res >= 0)
=======

  def size(list:List): BigInt = {list match {
    case Nil() => 0
    case Cons(x,xs) => 1 + size(xs)
  }} ensuring(res => res >= 0)
>>>>>>> b03689012b84b65708b49a01c70e68ceb6f413bf

  def length(l:List): BigInt = {
    l match {
      case Nil() => 0
      case Cons(x,xs) => 1 + length(xs)
    }
<<<<<<< HEAD
  } ensuring(res => res == size(l) /*&& tmpl((a,b) => time <= a*size(l) + b)*/)
=======
  } ensuring(res => res == size(l) && time <= ? *size(l) + ?)
>>>>>>> b03689012b84b65708b49a01c70e68ceb6f413bf

  def split(l:List,n:BigInt): (List,List) = {
    require(n >= 0 && n <= size(l))
    if (n <= 0) (Nil(),l)
    else
<<<<<<< HEAD
    l match {
        case Nil() => (Nil(),l)
        case Cons(x,xs) => {
          if(n == 1) (Cons(x,Nil()), xs)
          else {
            val (fst,snd) = split(xs, n-1)
            (Cons(x,fst), snd)
          }
        }
    }
  } ensuring(res => size(res._2) == size(l) - n && size(res._1) == n && size(res._2) + size(res._1) == size(l) /*&& tmpl((a,b) => time <= a*n +b)*/)
=======
	l match {
      case Nil() => (Nil(),l)
      case Cons(x,xs) => {
        if(n == 1) (Cons(x,Nil()), xs)
        else {
          val (fst,snd) = split(xs, n-1)
          (Cons(x,fst), snd)
        }
      }
	}
  } ensuring(res => size(res._2) + size(res._1) == size(l) && time <= ? *n + ?)
>>>>>>> b03689012b84b65708b49a01c70e68ceb6f413bf

  def merge(aList:List, bList:List):List = (bList match {
    case Nil() => aList
    case Cons(x,xs) =>
<<<<<<< HEAD
      aList match {
        case Nil() => bList
        case Cons(y,ys) =>
          if (y < x)
            Cons(y,merge(ys, bList))
          else
            Cons(x,merge(aList, xs))
     }
  }) ensuring(res => size(aList) + size(bList) == size(res) /*&& tmpl((a,b,c) => time <= a*size(aList) + b*size(bList) + c)*/)

  // @compose
=======
    	 aList match {
   	       case Nil() => bList
   	       case Cons(y,ys) =>
    	        if (y < x)
    		   Cons(y,merge(ys, bList))
     		else
		   Cons(x,merge(aList, xs))
   	 }
  }) ensuring(res => size(aList)+size(bList) == size(res) && time <= ? *size(aList) + ? *size(bList) + ?)

  @compose
>>>>>>> b03689012b84b65708b49a01c70e68ceb6f413bf
  def mergeSort(list:List):List = {
    list match {
      case Cons(x,Nil()) => list
      case Cons(_,Cons(_,_)) =>
<<<<<<< HEAD
        val lby2 = length(list)/2
        val (fst,snd) = split(list,lby2)
        merge(mergeSort(fst),mergeSort(snd))

      case _ => list
  }} ensuring(res => size(res) == size(list) &&
       //time <= ? * (size(list) * size(list)) + ? &&
       (if (size(list) >= 10) rec <= 1 * size(list) + 2 * log(size(list)) + 2 else true) &&
       //tpr <= ? * size(list) + ?
       true)


  // def mergeSort(list : List): (List, BigInt) = {
  //   val bd =
  //     list match {
  //       case Cons(x,Nil()) => (list, BigInt(0))
  //       case Cons(_,Cons(_,_)) => {
  //         val e23 = split(list, length(list) / BigInt(2));
  //         val e32 = mergeSort(e23._1);
  //         val e30 = mergeSort(e23._2);
  //         (merge(e32._1, e30._1), ((BigInt(2) + e32._2) + e30._2))
  //       }
  //       case _ => (list, BigInt(0))
  //     };
  //   (bd._1, bd._2)
  // }  ensuring(res => size(res._1) == size(list) &&
  //      //time <= ? * (size(list) * size(list)) + ? &&
  //      (if (size(list) >= 10) res._2 <= 1 * size(list) + 2 * log(size(list)) + 2 else true) &&
  //      //tpr <= ? * size(list) + ?
  //      true)
=======
         val lby2 = length(list)/2
    	 val (fst,snd) = split(list,lby2)
    	 merge(mergeSort(fst),mergeSort(snd))

      case _ => list
  }} ensuring(res => time <= ? *(size(list)*size(list)) + b && tpr <= ? *size(list) + ? && rec <= ? *size(list))
>>>>>>> b03689012b84b65708b49a01c70e68ceb6f413bf
}
