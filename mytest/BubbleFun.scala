object Bubble[29] {


    def isArray(a: Map[Int,Int], size: Int): Boolean = 
      if((size <= 0))
        false
      else
        isArrayRec(0, size, a)

    def isArrayRec(i: Int, size: Int, a: Map[Int,Int]): Boolean = 
      if ((i[27] >= size))
        true
      else {
        if (a.isDefinedAt(i))
          isArrayRec(i + 1, size, a)
        else
          false
      }


    def partitioned[14](a[8] : Map[Int,Int], size[9] : Int, l1[10] : Int, u1[11] : Int, l2[12] : Int, u2[13] : Int) : Boolean = (let (t[56] := while[109](l2[12], true, l1[10], l1[10], size[9], u2[13], l2[12], l2[12], u1[11], l1[10], a[8])) in
      t[56]._2)

    def sorted[7](a[3] : Map[Int,Int], size[4] : Int, l[5] : Int, u[6] : Int) : Boolean = (let (t[69] := while[126](true, l[5], l[5], u[6], a[3], size[4], l[5])) in
      t[69]._1)

    def sort[2](a: Map[Int,Int], size: Int) : Map[Int,Int] = {
      val i2 = size - 1 
      val t = 
      (let (t[94] := while[131](0, a[0], i[93], a[0], i[93], size[1], a[0])) in
        t[94]._2))



    def while[138](sortedArray[75] : Map[Int,Int], j[76] : Int, sortedArray[132] : Map[Int,Int], i[133] : Int, size[134] : Int, i[135] : Int, sortedArray[136] : Map[Int,Int], a[137] : Map[Int,Int]) : (Map[Int,Int], Int) = if ((j[76] < i[133]))
      while[138](if ((sortedArray[75](j[76]) > sortedArray[75]((j[76] + 1))))
        (((sortedArray[75] ∪ {(j[76] -> sortedArray[75]((j[76] + 1)))}) ∪ {((j[76] + 1) -> sortedArray[75](j[76]))}))
      else
        (sortedArray[75])._1, (j[76] + 1), sortedArray[132], i[133], size[134], i[135], sortedArray[136], a[137])
    else
      (sortedArray[75], j[76])

    @pre : (((j[38] ≥ l2[117]) ∧ ((j[38] + 1) ≤ u2[114])) ∧ ((i[118] == l1[110]) ∧ ((((((((l1[110] ≥ 0) ∧ (l1[110] ≤ u1[111])) ∧ (u1[111] < l2[117])) ∧ (l2[117] ≤ u2[114])) ∧ (u2[114] < size[112])) ∧ isArray[17](a[115], size[112])) ∧ (size[112] < 5)) ∧ ((j[113] == l2[117]) ∧ (((i[119] ≥ l1[110]) ∧ ((i[119] + 1) ≤ u1[111])) ∧ ((i[119] ≤ u1[111]) ∧ (j[116] == l2[117])))))))
    @post: (¬((#res._2 ≤ u2[114])) ∧ ((#res._2 ≥ l2[117]) ∧ ((#res._2 + 1) ≤ u2[114])))
    def while[120](isPartitionned[37] : Boolean, j[38] : Int, l1[110] : Int, u1[111] : Int, size[112] : Int, j[113] : Int, u2[114] : Int, a[115] : Map[Int,Int], j[116] : Int, l2[117] : Int, i[118] : Int, i[119] : Int) : (Boolean, Int) = if ((j[38] ≤ u2[114]))
      while[120](if ((a[115](i[119]) > a[115](j[38])))
        (false)
      else
        (isPartitionned[37])._1, (j[38] + 1), l1[110], u1[111], size[112], j[113], u2[114], a[115], j[116], l2[117], i[118], i[119])
    else
      (isPartitionned[37], j[38])

    @pre : (((i[47] ≥ l1[101]) ∧ ((i[47] + 1) ≤ u1[106])) ∧ ((((((((l1[101] ≥ 0) ∧ (l1[101] ≤ u1[106])) ∧ (u1[106] < l2[104])) ∧ (l2[104] ≤ u2[103])) ∧ (u2[103] < size[102])) ∧ isArray[17](a[108], size[102])) ∧ (size[102] < 5)) ∧ ((i[107] == l1[101]) ∧ (j[105] == l2[104]))))
    @post: (¬((#res._3 ≤ u1[106])) ∧ ((#res._3 ≥ l1[101]) ∧ ((#res._3 + 1) ≤ u1[106])))
    def while[109](j[45] : Int, isPartitionned[46] : Boolean, i[47] : Int, l1[101] : Int, size[102] : Int, u2[103] : Int, l2[104] : Int, j[105] : Int, u1[106] : Int, i[107] : Int, a[108] : Map[Int,Int]) : (Int, Boolean, Int) = if ((i[47] ≤ u1[106]))
      (let (t[49] := while[120](isPartitionned[46], l2[104], l1[101], u1[106], size[102], j[105], u2[103], a[108], l2[104], l2[104], i[107], i[47])) in
        while[109](t[49]._2, t[49]._1, (i[47] + 1), l1[101], size[102], u2[103], l2[104], j[105], u1[106], i[107], a[108]))
    else
      (j[45], isPartitionned[46], i[47])

    @pre : ((k[125] == l[121]) ∧ ((((isArray[17](a[123], size[124]) ∧ (size[124] < 5)) ∧ (l[121] ≥ 0)) ∧ (u[122] < size[124])) ∧ (l[121] ≤ u[122])))
    @post: ¬((#res._2 ≤ u[122]))
    def while[126](isSorted[61] : Boolean, k[62] : Int, l[121] : Int, u[122] : Int, a[123] : Map[Int,Int], size[124] : Int, k[125] : Int) : (Boolean, Int) = if ((k[62] ≤ u[122]))
      while[126](if ((a[123](k[62]) > a[123]((k[62] + 1))))
        (false)
      else
        (isSorted[61])._1, (k[62] + 1), l[121], u[122], a[123], size[124], k[125])
    else
      (isSorted[61], k[62])

    @pre : (((((i[85] ≥ 0) ∧ isArray[17](sortedArray[84], size[129])) ∧ partitioned[14](sortedArray[84], size[129], 0, i[85], (i[85] + 1), (size[129] - 1))) ∧ sorted[7](sortedArray[84], size[129], i[85], (size[129] - 1))) ∧ ((sortedArray[130] == a[127]) ∧ (((size[129] ≤ 5) ∧ isArray[17](a[127], size[129])) ∧ (i[128] == (size[129] - 1)))))
    @post: (¬((#res._3 > 0)) ∧ ((((#res._3 ≥ 0) ∧ isArray[17](#res._2, size[129])) ∧ partitioned[14](#res._2, size[129], 0, #res._3, (#res._3 + 1), (size[129] - 1))) ∧ sorted[7](#res._2, size[129], #res._3, (size[129] - 1))))
    def while[131](j[83] : Int, sortedArray[84] : Map[Int,Int], i[85] : Int, a[127] : Map[Int,Int], i[128] : Int, size[129] : Int, sortedArray[130] : Map[Int,Int]) : (Int, Map[Int,Int], Int) = if ((i[85] > 0))
      (let (t[87] := while[138](sortedArray[84], 0, sortedArray[84], i[85], size[129], i[128], sortedArray[130], a[127])) in
        while[131](t[87]._2, t[87]._1, (i[85] - 1), a[127], i[128], size[129], sortedArray[130]))
    else
      (j[83], sortedArray[84], i[85])

}
