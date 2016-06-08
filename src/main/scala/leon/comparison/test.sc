val list = List(1, 2, 2, 3)

val list2 = List(1, 2)

val diff1 = list.diff(list2)

val diff2 = list2.diff(list)

val diff = diff1 ++ diff2

list.diff(diff)

list.intersect(list2)
