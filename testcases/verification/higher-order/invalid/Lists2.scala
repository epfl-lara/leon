import leon.lang._
import leon.collection._


object Lists2 {

  /**
   * SORTING
   **/

  def isSorted[A](l: List[A])(implicit ord: (A, A) => Boolean): Boolean = l match {
    case Cons(h1, Cons(h2, _)) if !ord(h1, h2) => false
    case Cons(h, t) => isSorted(t)
    case Nil() => true
  }

  def sort[A](l: List[A])(implicit ord: (A, A) => Boolean): List[A] = {
    val (res, sres) = bubble(l)
    res
    /*
    if (sres) {
      sort(res)
    } else {
      res
    }
    */
  } ensuring {
    isSorted(_)
  }

  def bubble[A](l: List[A])(implicit ord: (A, A) => Boolean): (List[A], Boolean) = {
    l match {
      case Cons(h1, t1 @ Cons(h2, t2)) if !ord(h1, h2) => (Cons(h2, Cons(h1, t2)), true)
      case Cons(h1, t1) =>
        val (tres, sres) = bubble(t1)
        (Cons(h1, tres), sres)
      case Nil() =>
        (Nil[A](), false)
    }
  } ensuring { _ match {
    /*res =>
    res match {*/
      case (lr, sr) => if (!sr) isSorted(lr) else true
    //}
    }
  }

}

