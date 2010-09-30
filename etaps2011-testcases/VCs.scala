import scala.collection.immutable.Set

object VCs {
  def heapSortNoRepeat1(hContent: Set[Int], hMinusMaxContent: Set[Int], recListContent: Set[Int], isSortedRecList: Boolean) : Boolean = {
    require(
         (hContent != Set.empty[Int])
      && (hMinusMaxContent == hContent -- Set(hContent.max))
      && (recListContent == hMinusMaxContent ++ Set(hContent.max))
      && isSortedRecList
    )
     ((recListContent == hContent)
   && isSortedRecList
   && (hContent.max > hMinusMaxContent.max))
  } ensuring(_ == true)

  def heapSortNoRepeat2(isSortedAcc: Boolean, accContent: Set[Int], hContent: Set[Int], hMinusMaxContent: Set[Int], recListContent: Set[Int], isSortedRecList: Boolean) = {
    require(
         isSortedAcc
      && (accContent != Set.empty[Int])
      && (hContent != Set.empty[Int])
      && (accContent.min > hContent.max)
      && (hMinusMaxContent == hContent -- Set(hContent.max))
      && (recListContent == hMinusMaxContent ++ Set(hContent.max) ++ accContent)
      && isSortedRecList
    )
     ((recListContent == hContent ++ accContent)
   && isSortedRecList
   && (hContent.max < accContent.min)
   && isSortedAcc
   && ((Set(hContent.max) ++ accContent).min > hMinusMaxContent.max))
  } ensuring(_ == true)
}
