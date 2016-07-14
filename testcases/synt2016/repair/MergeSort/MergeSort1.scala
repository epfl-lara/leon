import leon.collection._

object MergeSort {

  def split(l : List[BigInt]) : (List[BigInt],List[BigInt]) = { l match {
    case Cons(a, Cons(b, t)) => 
      val (rec1, rec2) = split(t)
      (rec1, Cons(b, rec2)) // FIXME: Forgot a
    case other => (other, Nil[BigInt]())
  }} ensuring { res =>
    val (l1, l2) = res
    l1.size >= l2.size &&
    l1.size <= l2.size + 1 &&
    l1.size + l2.size == l.size &&
    l1.content ++ l2.content == l.content
  }

  def isSorted(l : List[BigInt]) : Boolean = l match {
    case Cons(x, t@Cons(y, _)) => x <= y && isSorted(t)
    case _ => true
  }

  def merge(l1 : List[BigInt], l2 : List[BigInt]) : List[BigInt] = {
    require(isSorted(l1) && isSorted(l2))
    (l1, l2) match {
      case (Cons(h1, t1), Cons(h2,t2)) => 
        if (h1 <= h2) 
          Cons(h1, merge(t1, l2))
        else 
          Cons(h2, merge(l1, t2))
      case (Nil(), _) => l2
      case (_, Nil()) => l1
    }
  } ensuring { res =>
    isSorted(res) &&
    res.size == l1.size + l2.size  &&
    res.content == l1.content ++ l2.content
  }

  def mergeSort(l : List[BigInt]) : List[BigInt] = { l match {
    case Nil() => l
    case Cons(_, Nil()) => l
    case other =>
      val (l1, l2) = split(other)
      merge(mergeSort(l1), mergeSort(l2))
  }} ensuring { res =>
    isSorted(res) &&
    res.content == l.content &&
    res.size == l.size
  }
}



