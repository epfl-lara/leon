import leon.lang._

object MergeSort {

  abstract class List {
    def size : Int = this match {
      case Nil() => 0
      case Cons(_, tl) => 1 + tl.size
    }
    def content : Set[Int] = this match {
      case Nil() => Set.empty[Int]
      case Cons(hd, tl) => tl.content ++ Set(hd)
    }
  }

  case class Nil() extends List
  case class Cons(hd : Int, tl : List) extends List

  def split(l : List) : (List,List) = { l match {
    case Cons(a, Cons(b, t)) => 
      val (rec1, rec2) = split(t)
      (rec1, rec2) //FIXME forgot a and b
    case other => (other, Nil())
  }} ensuring { res =>
    val (l1, l2) = res
    l1.size >= l2.size &&
    l1.size <= l2.size + 1 &&
    l1.size + l2.size == l.size &&
    l1.content ++ l2.content == l.content
  }

  def isSorted(l : List) : Boolean = l match {
    case Cons(x, t@Cons(y, _)) => x <= y && isSorted(t)
    case _ => true
  }

  def merge(l1 : List, l2 : List) : List = {
    require(isSorted(l1) && isSorted(l2))
    (l1, l2) match {
      case (Cons(h1, t1), Cons(h2,t2)) => 
        if (h1 <= h2) 
          Cons(h1, merge(t1, l2))
        else 
          Cons(h2, merge(l1, t2))
      case (Nil(), _) => l2
      case (_, Nil()) => l1
    }
  } ensuring { res =>
    isSorted(res) &&
    res.size == l1.size + l2.size  &&
    res.content == l1.content ++ l2.content
  }

  def mergeSort(l : List) : List = { l match {
    case Nil() => l
    case Cons(_, Nil()) => l
    case other =>
      val (l1, l2) = split(other)
      merge(mergeSort(l1), mergeSort(l2))
  }} ensuring { res =>
    isSorted(res) &&
    res.content == l.content &&
    res.size == l.size
  }
}



