import scala.collection.immutable.Set

object VCs {
  def forFun1(a: Set[Int], b: Set[Int], n: Int) : Boolean = {
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

  def heapSortNoRepeat1(hContent: Set[Int], hMinusMaxContent: Set[Int], recListContent: Set[Int]) : Boolean = {
    require(
         (hContent != Set.empty[Int])
      && (hMinusMaxContent == hContent -- Set(hContent.max))
      && (recListContent == hMinusMaxContent ++ Set(hContent.max))
    )
     ((recListContent == hContent)
   && (hContent.max > hMinusMaxContent.max))
  } ensuring(_ == true)

  def heapSortNoRepeat2(accContent: Set[Int], hContent: Set[Int], hMinusMaxContent: Set[Int], recListContent: Set[Int]) = {
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
