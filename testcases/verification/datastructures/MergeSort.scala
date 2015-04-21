import leon.lang._

object MergeSort {
  sealed abstract class List
  case class Cons(head:Int,tail:List) extends List
  case class Nil() extends List

  case class Pair(fst:List,snd:List)

  def contents(l: List): Set[Int] = l match {
    case Nil() => Set.empty
    case Cons(x,xs) => contents(xs) ++ Set(x)
  }

  def is_sorted(l: List): Boolean = l match {
    case Nil() => true
    case Cons(x,xs) => xs match {
      case Nil() => true
      case Cons(y, ys) => x <= y && is_sorted(Cons(y, ys))
    }
  }

  def length(list:List): Int = list match {
    case Nil() => 0
    case Cons(x,xs) => 1 + length(xs)
  }

  def splithelper(aList:List,bList:List,n:Int): Pair =
    if (n <= 0) Pair(aList,bList)
    else
    bList match {
              case Nil() => Pair(aList,bList)
              case Cons(x,xs) => splithelper(Cons(x,aList),xs,n-1)
    }

  def split(list:List,n:Int): Pair = splithelper(Nil(),list,n)

  def merge(aList:List, bList:List):List = (bList match {
    case Nil() => aList
    case Cons(x,xs) =>
         aList match {
           case Nil() => bList
           case Cons(y,ys) =>
                if (y < x)
               Cons(y,merge(ys, bList))
            else
           Cons(x,merge(aList, xs))
     }
  }) ensuring(res => contents(res) == contents(aList) ++ contents(bList))

  def mergeSort(list:List):List = (list match {
    case Nil() => list
    case Cons(x,Nil()) => list
    case _ =>
         val p = split(list,length(list)/2)
     merge(mergeSort(p.fst), mergeSort(p.snd))
  }) ensuring(res => contents(res) == contents(list) && is_sorted(res))


  def main(args: Array[String]): Unit = {
    val ls: List = Cons(5, Cons(2, Cons(4, Cons(5, Cons(1, Cons(8,Nil()))))))
    println(ls)
    println(mergeSort(ls))
  }
}
