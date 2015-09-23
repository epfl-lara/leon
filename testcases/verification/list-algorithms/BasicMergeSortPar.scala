/* Basic parallel Merge sort that: 
   * shows use of 'par' construct
   * uses a higher-order comparison function
   * relies on a strong spec for a list library function splitAtIndex
   Warning: spec does not check sortedness or multiplicity.
*/
import leon.lang._
import leon.collection._
import leon.par._
object MergeSortPar {

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

  def msort[T](less: (T, T) => Boolean)(l: List[T], len : BigInt): List[T] = {
    require(len == l.length)
    if (l.size <= 1) l
    else {
      val c = len/2
      val (first, second) = l.splitAtIndex(c) // evenSplit
      val (s1, s2) = parallel(msort(less)(first, c), msort(less)(second, len - c))
      merge(less)(s1, s2)
    }
  } ensuring { res => res.content == l.content && 
                      res.size == l.size }
}
