object BubbleFun {

    // --------------------- sort ----------------------

    def sort(a: Map[Int,Int], size: Int): Map[Int,Int] = {
      val i = size - 1
      val t = sortWhile(0, a, i, a, i, size, a)
      t._2
    }

    def sortWhile(
      j: Int, sortedArray: Map[Int,Int], i: Int, a: Map[Int,Int], i2: Int, 
      size: Int, sortedArray2 : Map[Int,Int]) : (Int, Map[Int,Int], Int) = 
        if ((i > 0)) {
          val t = sortNestedWhile(sortedArray, 0, sortedArray, i, size, i2, sortedArray2, a)
          sortWhile(t._2, t._1, i - 1, a, i2, size, sortedArray2)
        } else (j, sortedArray, i)


    def sortNestedWhile(
      sortedArray: Map[Int,Int], j: Int, sortedArray2 : Map[Int,Int], i: Int, 
      size: Int, i2: Int, sortedArray3: Map[Int,Int], a: Map[Int,Int]) : (Map[Int,Int], Int) =
        if(j < i) {
          val newSortedArray = 
            if(sortedArray(j) > sortedArray(j + 1))
              sortedArray.updated(j, sortedArray(j + 1)).updated(j+1, sortedArray(j))
            else
              sortedArray
          sortNestedWhile(newSortedArray, (j + 1), sortedArray2, i, size, i2, sortedArray3, a)
        } else (sortedArray, j)

    //  --------------------- sorted --------------------

    def sorted(a: Map[Int,Int], size: Int, l: Int, u: Int) : Boolean = {
      val t = sortedWhile(true, l, l, u, a, size, l)
      t._1
    }

    def sortedWhile(
      isSorted: Boolean, k: Int, l: Int, u: Int, 
      a: Map[Int,Int], size: Int, k2 : Int) : (Boolean, Int) = 
        if ((k <= u)) {
          sortedWhile(
            if (a(k) > a(k + 1)) false else isSorted, k + 1, l, u, a, size, k2)
        } else (isSorted, k)


    // ------------- partitioned ------------------

    def partitioned(a: Map[Int,Int], size: Int, l1: Int, u1: Int, l2: Int, u2: Int) : Boolean = {
      val t = partitionedWhile(l2, true, l1, l1, size, u2, l2, l2, u1, l1, a)
      t._2
    }

    def partitionedWhile(
      j: Int, isPartitionned: Boolean, i: Int, l1: Int, size: Int, u2: Int, 
      l2: Int, j2: Int, u1: Int, i2 : Int, a: Map[Int,Int]) : (Int, Boolean, Int) =
        if((i <= u1)) {
          val t = partitionedNestedWhile(
                    isPartitionned, l2, l1, u1, size, j2, u2, a, l2, l2, i2, i
                  )
          partitionedWhile(t._2, t._1, i + 1, l1, size, u2, l2, j2, u1, i2, a)
        } else (j, isPartitionned, i)

    def partitionedNestedWhile(
      isPartitionned: Boolean, j: Int, l1: Int, u1: Int, size: Int, j2: Int, u2: Int, 
      a: Map[Int,Int], j3 : Int, l2: Int, i2: Int, i: Int) : (Boolean, Int) =
        if (j <= u2) {
          partitionedNestedWhile(
            (if ((a(i) > a(j)))
              false
            else
              isPartitionned), 
            j + 1, l1, u1, size, j2, u2, a, j3, l2, i2, i)
        } else (isPartitionned, j)

    //------------ isArray -------------------

    def isArray(a: Map[Int,Int], size: Int): Boolean = 
      if((size <= 0))
        false
      else
        isArrayRec(0, size, a)

    def isArrayRec(i: Int, size: Int, a: Map[Int,Int]): Boolean = 
      if (i >= size)
        true
      else {
        if (a.isDefinedAt(i))
          isArrayRec(i + 1, size, a)
        else
          false
      }


}
