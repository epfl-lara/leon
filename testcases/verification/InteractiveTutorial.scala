import leon.lang._

object Lists {

  /* (1) Define type */
  //abstract class List[A]
  case class Cons[A](h: A, tl: List[A]) extends List[A]
  case class Nil[A]() extends List[A]

  /* (2.1) write a recursive size implementation (beware of overflow)
     (2.2) prove that result is positive
   */
  def size[A](l: List[A]): BigInt = (l match {
    case Nil() => BigInt(0)
    case Cons(_, t) => 1 + size(t)
  }) ensuring(res => res >= 0)

  /* (3.1) Alternative implementation of size using imperative style */

  /* (3.2) define helpers 
     (3.3) add requirements on head/tail 
   */
  abstract class List[A] {
    def isEmpty: Boolean = this match {
      case Nil() => true
      case _ => false
    }
    def nonEmpty: Boolean = !isEmpty

    /* (4.2) */
    def content: Set[A] = this match {
      case Nil() => Set[A]()
      case Cons(x, xs) => xs.content ++ Set(x)
    }

    def head: A = {
      require(nonEmpty)
      this match {
        case Cons(h, _) => h
      }
    }
    def tail: List[A] = {
      require(nonEmpty)
      this match {
        case Cons(_, t) => t
      }
    }
  }

  /* (3.4) new size implementation */
  //def size2[A](l: List[A]): BigInt = {
  //  var res: BigInt = 0
  //  var lst: List[A] = l
  //  while(lst.nonEmpty) {
  //    lst = lst.tail
  //    res += 1
  //  }
  //  //(while(!isEmpty(lst)) {
  //  //  lst = tail(lst)
  //  //  res += 1
  //  //}) invariant(res + sizeSpec(lst) == sizeSpec(l))
  //  res
  //}// ensuring(res => res == sizeSpec(l))

  /* (3.5) prove equivalence */
  def size2[A](l: List[A]): BigInt = {
    var res: BigInt = 0
    var lst: List[A] = l
    (while(lst.nonEmpty) {
      lst = lst.tail
      res += 1
    }) invariant(res + size(lst) == size(l))
    res
  } ensuring(res => res == size(l))


  /* (4) Sorting */

  /* (4.1) the isSorted predicate, only on lists of bigint */
  def isSorted(l: List[BigInt]): Boolean = l match {
    case Nil() => true
    case Cons(x, Nil()) => true
    case Cons(x, Cons(y, ys)) => x <= y && isSorted(Cons(y, ys))
  }

  /* (4.2) add content to List def */

  /* (4.3.1) insert that preserve the order, without require first 
   * (4.3.2) show counterexample
   * (4.3.3) add proper require
   */
  def sortedIns(e: BigInt, l: List[BigInt]): List[BigInt] = {
    require(isSorted(l))
    l match {
      case Nil() => Cons(e,Nil())
      case Cons(x,xs) => if (x <= e) Cons(x, sortedIns(e, xs)) else Cons(e, l)
    }
  } ensuring(res => res.content == l.content ++ Set(e) && 
                    isSorted(res) && 
                    size(res) == size(l) + 1)


  /* (4.4) finally, sort implementation and specs */
  def sort(l: List[BigInt]): List[BigInt] = (l match {
    case Nil() => Nil[BigInt]()
    case Cons(x,xs) => sortedIns(x, sort(xs))
  }) ensuring(res => res.content == l.content && 
                     isSorted(res) && 
                     size(res) == size(l))

  /* (4.5) also able to do merge-sort, with merge operation */
  def merge(l1: List[BigInt], l2: List[BigInt]): List[BigInt] = {
    require(isSorted(l1) && isSorted(l2))
    (l1, l2) match {
      case (Nil(), _) => l2
      case (_, Nil()) => l1
      case (Cons(h1,t1), Cons(h2, t2)) =>
        if (h1 <= h2) Cons(h1, merge(t1, l2))
        else          Cons(h2, merge(l1, t2))
    }
  } ensuring { 
    (res: List[BigInt]) =>
      isSorted(res) && 
      res.content == l1.content ++ l2.content &&
      size(res) == size(l1) + size(l2)}

  /* (4.6) split the list */
  def split(l: List[BigInt]): (List[BigInt], List[BigInt]) = {
    require(size(l) > 1)
    l match {
      case Cons(h1, Cons(h2, Nil())) =>
        (Cons(h1, Nil()), Cons(h2, Nil()))
      case Cons(h1, Cons(h2, Cons(h3, Nil()))) =>
        (Cons(h1, Cons(h3, Nil())), Cons(h2, Nil()))
      case Cons(h1, Cons(h2, tail)) =>
        val (rec1, rec2) = split(tail)
        (Cons(h1, rec1), Cons(h2, rec2))
      case _ => (l, Nil[BigInt]())
    }
  } ensuring { (res: (List[BigInt], List[BigInt])) =>
    val (r1, r2) = res
    size(r1) < size(l) && size(r2) < size(l) &&
    size(r1) + size(r2) == size(l) &&
    r1.content ++ r2.content == l.content
  }

  /* (4.7) merge sort implementation */
  def mergeSort(l: List[BigInt]): List[BigInt] = {
    if (size(l) <= 1) l else {
      val (l1, l2) = split(l)
      merge(mergeSort(l1), mergeSort(l2))
    }
  } ensuring ( res =>
    isSorted(res) && 
    res.content == l.content &&
    size(res) == size(l)
  )


  /* (5) Higher-order functions */

  /* (5.1) Map */
  def map[A, B](l: List[A], f: A => B): List[B] = (l match {
    case Nil() => Nil[B]()
    case Cons(h, t) => Cons(f(h), map(t, f))
  }) ensuring( (res: List[B]) => size(res) == size(l) )

  /* (5.2) Forall */
  def forall[A](l: List[A], p: A => Boolean): Boolean = l match {
    case Nil() => true
    case Cons(h, t) => p(h) && forall(t, p)
  }

  /* (5.3) filter */
  def filter[A](l: List[A], p: A => Boolean): List[A] = (l match {
    case Nil() => Nil[A]()
    case Cons(h, t) if p(h) => Cons(h, filter(t, p))
    case Cons(_, t) => filter(t, p)
  }) ensuring { res =>
    size(res) <= size(l) &&
    res.content.subsetOf(l.content) &&
    forall(res, p)
  }

}

