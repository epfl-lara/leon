import leon.lang._

object BubbleFun {

    // --------------------- sort ----------------------

    def sort(a: Map[Int,Int], size: Int): Map[Int,Int] = ({
      require(isArray(a, size) && size < 5)

      val i = size - 1
      val t = sortWhile(0, a, i, size)
      t._2
    }) ensuring(res => isArray(res, size) && sorted(res, size, 0, size-1) /*&& content(res, size) == content(a, size)*/)

    def sortWhile(j: Int, sortedArray: Map[Int,Int], i: Int, size: Int) : (Int, Map[Int,Int], Int) = ({
      require(i >= 0 && i < size && isArray(sortedArray, size) && size < 5 &&
              sorted(sortedArray, size, i, size - 1) &&
              partitioned(sortedArray, size, 0, i, i+1, size-1))

      if (i > 0) {
        val t = sortNestedWhile(sortedArray, 0, i, size)
        sortWhile(t._2, t._1, i - 1, size)
      } else (j, sortedArray, i)
    }) ensuring(res => isArray(res._2, size) &&
                       sorted(res._2, size, res._3, size - 1) &&
                       partitioned(res._2, size, 0, res._3, res._3+1, size-1) &&
                       res._3 >= 0 && res._3 <= 0 /*&& content(res._2, size) == content(sortedArray, size)*/
               )


    def sortNestedWhile(sortedArray: Map[Int,Int], j: Int, i: Int, size: Int) : (Map[Int,Int], Int) = ({
      require(j >= 0 && j <= i && i < size && isArray(sortedArray, size) && size < 5 &&
              sorted(sortedArray, size, i, size - 1) &&
              partitioned(sortedArray, size, 0, i, i+1, size-1) &&
              partitioned(sortedArray, size, 0, j-1, j, j))
      if(j < i) {
        val newSortedArray =
          if(sortedArray(j) > sortedArray(j + 1))
            sortedArray.updated(j, sortedArray(j + 1)).updated(j+1, sortedArray(j))
          else
            sortedArray
        sortNestedWhile(newSortedArray, j + 1, i, size)
      } else (sortedArray, j)
    }) ensuring(res => isArray(res._1, size) &&
                       sorted(res._1, size, i, size - 1) &&
                       partitioned(res._1, size, 0, i, i+1, size-1) &&
                       partitioned(res._1, size, 0, res._2-1, res._2, res._2) &&
                       res._2 >= i && res._2 >= 0 && res._2 <= i /*&& content(res._1, size) == content(sortedArray, size)*/)


    //some intermediate results
    def lemma1(a: Map[Int, Int], size: Int, i: Int): Boolean = ({
      require(isArray(a, size) && size < 5 && sorted(a, size, i, size-1) && partitioned(a, size, 0, i, i+1, size-1) && i >= 0 && i < size)
      val t = sortNestedWhile(a, 0, i, size)
      val newJ = t._2
      i == newJ
    }) ensuring(_ == true)
    def lemma2(a: Map[Int, Int], size: Int, i: Int): Boolean = ({
      require(isArray(a, size) && size < 5 && sorted(a, size, i, size-1) && partitioned(a, size, 0, i, i+1, size-1) && i >= 0 && i < size)
      val t = sortNestedWhile(a, 0, i, size)
      val newA = t._1
      val newJ = t._2
      partitioned(newA, size, 0, i-1, i, i)
    }) ensuring(_ == true)
    def lemma3(a: Map[Int, Int], size: Int, i: Int): Boolean = ({
      require(partitioned(a, size, 0, i, i+1, size-1) && partitioned(a, size, 0, i-1, i, i) && isArray(a, size) && size < 5 && i >= 0 && i < size)
      partitioned(a, size, 0, i-1, i, size-1)
    }) ensuring(_ == true)
    def lemma4(a: Map[Int, Int], size: Int, i: Int): Boolean = ({
      require(isArray(a, size) && size < 5 && sorted(a, size, i, size-1) && partitioned(a, size, 0, i, i+1, size-1) && i >= 0 && i < size)
      val t = sortNestedWhile(a, 0, i, size)
      val newA = t._1
      partitioned(newA, size, 0, i-1, i, size-1)
    }) ensuring(_ == true)


    //  --------------------- sorted --------------------
    def sorted(a: Map[Int,Int], size: Int, l: Int, u: Int) : Boolean = {
      require(isArray(a, size) && size < 5 && l >= 0 && l <= u && u < size)
      val t = sortedWhile(true, l, l, u, a, size)
      t._1
    }

    def sortedWhile(isSorted: Boolean, k: Int, l: Int, u: Int, a: Map[Int,Int], size: Int) : (Boolean, Int) = {
      require(isArray(a, size) && size < 5 && l >= 0 && l <= u && u < size && k >= l && k <= u)
      if(k < u) {
        sortedWhile(if(a(k) > a(k + 1)) false else isSorted, k + 1, l, u, a, size)
      } else (isSorted, k)
    }



    // ------------- partitioned ------------------
    def partitioned(a: Map[Int,Int], size: Int, l1: Int, u1: Int, l2: Int, u2: Int) : Boolean = {
      require(isArray(a, size) && size < 5 && l1 >= 0 && u1 < l2 && u2 < size)
      if(l2 > u2 || l1 > u1)
        true
      else {
        val t = partitionedWhile(l2, true, l1, l1, size, u2, l2, u1, a)
        t._2
      }
    }
    def partitionedWhile(j: Int, isPartitionned: Boolean, i: Int, l1: Int, size: Int, u2: Int, l2: Int, u1: Int, a: Map[Int,Int]) : (Int, Boolean, Int) = {
      require(isArray(a, size) && size < 5 && l1 >= 0 && l1 <= u1 && u1 < l2 && l2 <= u2 && u2 < size && i >= l1)

      if(i <= u1) {
        val t = partitionedNestedWhile(isPartitionned, l2, i, l1, u1, size, u2, a, l2)
        partitionedWhile(t._2, t._1, i + 1, l1, size, u2, l2, u1, a)
      } else (j, isPartitionned, i)
    }
    def partitionedNestedWhile(isPartitionned: Boolean, j: Int, i: Int, l1: Int, u1: Int, size: Int, u2: Int, a: Map[Int,Int], l2: Int): (Boolean, Int) = {
      require(isArray(a, size) && size < 5 && l1 >= 0 && l1 <= u1 && u1 < l2 && l2 <= u2 && u2 < size && j >= l2 && i >= l1 && i <= u1)

      if (j <= u2) {
        partitionedNestedWhile(
          (if (a(i) > a(j))
            false
          else
            isPartitionned),
          j + 1, i, l1, u1, size, u2, a, l2)
      } else (isPartitionned, j)
    }


    //------------ isArray -------------------
    def isArray(a: Map[Int,Int], size: Int): Boolean =
      if(size <= 0)
        false
      else
        isArrayRec(0, size, a)

    def isArrayRec(i: Int, size: Int, a: Map[Int,Int]): Boolean =
      if (i >= size)
        true
      else {
        if(a.isDefinedAt(i))
          isArrayRec(i + 1, size, a)
        else
          false
      }


    // ----------------- content ------------------
    def content(a: Map[Int, Int], size: Int): Set[Int] = {
      require(isArray(a, size) && size < 5)
      contentRec(a, size, 0)
    }

    def contentRec(a: Map[Int, Int], size: Int, i: Int): Set[Int] = {
      require(isArray(a, size) && i >= 0)
      if(i < size)
        Set(a(i)) ++ contentRec(a, size, i+1)
      else
        Set.empty[Int]
    }

}
