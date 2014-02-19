import leon.lang._

object QuickSortImp {


  def quicksort(array: Array[Int]): Array[Int] = {
    require(array.length > 0)

    def quicksort0(array: Array[Int], left: Int, right: Int): Array[Int] = {
      require(array.length > 0 && left >= 0 && right < array.length)

      def partition(array: Array[Int], left: Int, right: Int, pivotIndex: Int): (Array[Int], Int) = {
        require(array.length > 0 && left >= 0 && left < right && right < array.length &&
                pivotIndex >= left && pivotIndex <= right)
        val pivotValue = array(pivotIndex)
        val sa: Array[Int] = array.clone
        val tmp = array(pivotIndex)
        sa(pivotIndex) = sa(right)
        sa(right) = tmp
        var storeIndex = left
        var i = left
        (while(i < right) {
          if(sa(i) < pivotValue) {
            val tmp = sa(i)
            sa(i) = sa(storeIndex)
            sa(storeIndex) = tmp
            storeIndex = storeIndex + 1
          }
          i += 1
        }) invariant(
              sa.length >= 0 && right < sa.length && sa.length == array.length &&
              storeIndex >= left &&
              i >= left &&
              storeIndex <= i &&
              storeIndex <= right &&
              i <= right
            )

        val tmp2 = array(storeIndex)
        //sa(storeIndex) = sa(right)
        sa(pivotIndex) = sa(right)
        sa(right) = tmp2

        (sa, storeIndex)
      } ensuring(res => res._2 >= left && res._2 <= right &&
                        res._1.length == array.length && res._1.length >= 0)


      // If the list has 2 or more items
      if(left < right) {
        val pivotIndex = left

        val (as1, pivotNewIndex) = partition(array, left, right, pivotIndex)

        // Recursively sort elements smaller than the pivot
        val as2 = quicksort0(as1, left, pivotNewIndex - 1)

        // Recursively sort elements at least as big as the pivot
        quicksort0(as2, pivotNewIndex + 1, right)
      } else array
    } ensuring(res => res.length == array.length && res.length >= 0)

    quicksort0(array, 0, array.length-1)
  } ensuring(res =>  sorted(res, 0, res.length-1))
                    
  def sorted(a: Array[Int], l: Int, u: Int): Boolean = {
    require(a.length >= 0 && l >= 0 && u < a.length && l <= u)
    var k = l
    var isSorted = true
    (while(k < u) {
      if(a(k) > a(k+1))
        isSorted = false
      k = k + 1
    }) invariant(k <= u && k >= l)
    isSorted
  }


}
