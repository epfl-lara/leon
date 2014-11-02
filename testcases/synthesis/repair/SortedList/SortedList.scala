import leon.collection._
import leon.lang.synthesis._

object SortedList {

  def isSorted(l : List[Int]) : Boolean = l match {
    case Cons(h1, tl@Cons(h2, _)) => h1 <= h2 && isSorted(tl)
    case _ => true
  }

  def merge(l1 : List[Int], l2 : List[Int]) : List[Int] = { 
    require(isSorted(l1) && isSorted(l2))
    (l1, l2) match {
      case (Nil(), _) => l2
      case (_, Nil()) => l1
      case (Cons(h1, t1), Cons(h2,t2)) =>
        if (h1 <= h2) 
          Cons(h1, merge(t1,l2))
        else 
          Cons(h2, merge(l1,t2))
    }
  } ensuring { res =>
    isSorted(res) && (res.content == l1.content ++ l2.content)
  }

  
  def split(l : List[Int]) : (List[Int], List[Int]) = { l match {
    case Cons(h1, Cons(h2, tl)) => 
      val (t1,t2) = split(tl)
      ( Cons(h1,t1), Cons(h2,t2) )
    case _ => (l, Nil[Int]())
  }} ensuring { res =>
    val (res1,res2) = res
    res1.content ++ res2.content == l.content &&
    res1.size + res2.size == l.size &&
    res1.size <= res2.size + 1 &&
    res1.size >= res2.size - 1
  }

  def mergeSort(l : List[Int]) : List[Int] = { l match {
    case Nil() => l 
    case Cons(_, Nil()) => l
    case _ => 
      val (l1, l2) = split(l)
      merge(mergeSort(l1),mergeSort(l2))
  }} ensuring { res =>
    res.content == l.content &&
    isSorted(res)
  }

}
