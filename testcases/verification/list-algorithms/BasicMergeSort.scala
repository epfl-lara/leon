import leon.lang._
import leon.collection._
object MergeSort {

  def merge[T](less: (T, T) => Boolean)(xs: List[T], ys: List[T]): List[T] = {
    (xs, ys) match {
      case (Nil(), _) => ys
      case (_, Nil()) => xs
      case (Cons(x,xtail), Cons(y,ytail)) =>
        if (less(x, y))
          x :: merge(less)(xtail, ys)
        else
          y :: merge(less)(xs, ytail)
    }
  } ensuring { res => res.content == xs.content ++ ys.content &&
                      res.size == xs.size + ys.size }

  def msort[T](less: (T, T) => Boolean)(l: List[T]): List[T] = {
    if (l.size <= 1) l
    else {
      val c = l.length/2
      val (first, second) = l.splitAtIndex(c) // evenSplit
      merge(less)(msort(less)(first), msort(less)(second))
    }
  } ensuring { res => res.content == l.content && res.size == l.size }
}
