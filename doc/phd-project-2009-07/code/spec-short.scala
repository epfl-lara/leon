$\forall$ xs: List[Int], ys: List[Int], z: Int .
  content(xs) == content(ys) ==> content(insert(z, xs)) == content(insert(z, ys))
