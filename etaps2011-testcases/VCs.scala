import scala.collection.immutable.Set

object VCs {
  def forFun1_V(a: Set[Int], b: Set[Int], n: Int) : Boolean = {
    require(
        (a != Set.empty[Int])
     && (a.min == 0)
     && (a.max == n - 1)
     && (a.size == n)
     && (b subsetOf a)
     && (b != a)
    )
      a.contains(b.size)
  } ensuring(_ == true)

  def forFun2_V(a: Set[Int], b: Set[Int], n: Int) : Boolean = {
    require(
        (a != Set.empty[Int])
     && (a.min == 1)
     && (a.max == n)
     && (a.size == n)
     && (b subsetOf a)
     && (b != Set.empty[Int])
    )
      a.contains(b.size)
  } ensuring(_ == true)

  def paperBSTFind_V(c: Set[Int], l: Set[Int], r: Set[Int], v: Int, range1: Set[Int], range2: Set[Int], range3: Set[Int]) : Boolean = {
    require(
         (c == l ++ Set(v) ++ r)
      && (l.max < v)
      && (v < r.min)
      && (range1 ++ range2 ++ range3 == c)
      && (range1.max < range2.min)
      && (range2.min < range3.max)
      && (range1.size == l.size)
      && (range2.size == 1)
      && (range3.size == c.size - l.size - 1)
    )
      Set(v) == range2
  } ensuring(_ == true)

  def paperPartitionPivot_V(above: Set[Int], pivot: Int, e: Int, abovePrime: Set[Int]) : Boolean = {
    require(
         (above == Set.empty[Int] || pivot < above.min)
      && !(e <= pivot)
      && (abovePrime == above ++ Set(e))
    )
      pivot < abovePrime.min
  } ensuring(_ == true)

  def heapSortNoRepeat1_V(hContent: Set[Int], hMinusMaxContent: Set[Int], recListContent: Set[Int]) : Boolean = {
    require(
         (hContent != Set.empty[Int])
      && (hMinusMaxContent == hContent -- Set(hContent.max))
      && (recListContent == hMinusMaxContent ++ Set(hContent.max))
    )
     ((recListContent == hContent)
   && (hContent.max > hMinusMaxContent.max))
  } ensuring(_ == true)

  def heapSortNoRepeat2_V(accContent: Set[Int], hContent: Set[Int], hMinusMaxContent: Set[Int], recListContent: Set[Int]) = {
    require(
         (accContent != Set.empty[Int])
      && (hContent != Set.empty[Int])
      && (accContent.min > hContent.max)
      && (hMinusMaxContent == hContent -- Set(hContent.max))
      && (recListContent == hMinusMaxContent ++ Set(hContent.max) ++ accContent)
    )
     ((recListContent == hContent ++ accContent)
   && (hContent.max < accContent.min)
   && ((Set(hContent.max) ++ accContent).min > hMinusMaxContent.max))
  } ensuring(_ == true)
}
