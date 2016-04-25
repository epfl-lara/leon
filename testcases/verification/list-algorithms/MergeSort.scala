import leon.lang._
import synthesis._
import leon.collection._

object MergeSort {

  def isSorted(l: List[BigInt]): Boolean = l match {
    case Cons(x, t@Cons(y, _)) => x <= y && isSorted(t)
    case _ => true
  }

  def merge(l1: List[BigInt], l2: List[BigInt]): List[BigInt] = {
    require(isSorted(l1) && isSorted(l2))
    (l1, l2) match {
      case (Nil(), _) => l2
      case (_, Nil()) => l1
      case (Cons(h1,t1), Cons(h2, t2)) =>
        if (h1 <= h2) Cons(h1, merge(t1, l2))
        else          Cons(h2, merge(l1, t2))
    }
  } ensuring { 
    (res: List[BigInt]) =>
      isSorted(res) && 
      res.content == l1.content ++ l2.content &&
      res.size == l1.size + l2.size
  }

  def split(l: List[BigInt]): (List[BigInt], List[BigInt]) = {
    require(l.size > 1)
    l match {
      case Cons(h1, Cons(h2, Nil())) =>
        (List(h1), List(h2))
      case Cons(h1, Cons(h2, Cons(h3, Nil()))) =>
        (List(h1, h3), List(h2))
      case Cons(h1, Cons(h2, tail)) =>
        val (rec1, rec2) = split(tail)
        (h1 :: rec1, h2 :: rec2)
      case _ => (l, Nil[BigInt]())
    }
  } ensuring { (res: (List[BigInt], List[BigInt])) =>
    val (r1, r2) = res
    r1.size < l.size && r2.size < l.size &&
    r1.size + r2.size == l.size &&
    r1.content ++ r2.content == l.content
  }

  def mergeSort(l: List[BigInt]): List[BigInt] = {
    if (l.size <= 1) l else {
      val (l1, l2) = split(l)
      merge(mergeSort(l1), mergeSort(l2))
    }
  } ensuring ( res =>
    isSorted(res) && 
    res.content == l.content &&
    res.size == l.size
  )

}
