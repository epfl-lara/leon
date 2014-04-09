import leon.annotation._
import leon.lang._
import leon.lang.synthesis._

// Sorting lists is a fundamental problem in CS.
object Sorting {
  // Data types
  sealed abstract class List
  case class Cons(head : Int, tail : List) extends List
  case class Nil() extends List

  sealed abstract class LList
  case class LCons(head : List, tail : LList) extends LList
  case class LNil() extends LList

  // Abstraction functions
  def content(list : List) : Set[Int] = list match {
    case Nil() => Set.empty[Int]
    case Cons(x, xs) => Set(x) ++ content(xs)
  }

  def lContent(llist : LList) : Set[Int] = llist match {
    case LNil() => Set.empty[Int]
    case LCons(x, xs) => content(x) ++ lContent(xs)
  }

  def size(list : List) : Int = (list match {
    case Nil() => 0
    case Cons(_, xs) => 1 + size(xs)
  }) ensuring(_ >= 0)

  def isSorted(list : List) : Boolean = list match {
    case Nil() => true
    case Cons(_, Nil()) => true
    case Cons(x1, Cons(x2, _)) if(x1 > x2) => false
    case Cons(_, xs) => isSorted(xs)
  }

  def lIsSorted(llist : LList) : Boolean = llist match {
    case LNil() => true
    case LCons(x, xs) => isSorted(x) && lIsSorted(xs)
  }

  @induct
  def sortedLemma(a: Int, x: Int, b: List) = {
    !(isSorted(Cons(a,b)) && (content(b) contains x)) || (x >= a)
  } holds

  def abs(i : Int) : Int = {
    if(i < 0) -i else i
  } ensuring(_ >= 0)

  /***************************
   *                         *
   *    I N S E R T I O N    *
   *                         *
   ***************************/

  def insertSpec(elem : Int, list : List, res : List) : Boolean = {
//    isSorted(list) && // Part of precondition, really.
    isSorted(res) && content(res) == content(list) ++ Set(elem)
  }

  def insert(elem : Int, list : List) : List = {
    require(isSorted(list))
    choose { (res : List) => insertSpec(elem, list, res) }
  }

    //require(head < elem && isSorted(Cons(head, tail)) && r == insertImpl(elem, tail))
    //require(head < elem && isSorted(Cons(head, tail)) && isSorted(r) && content(r) == content(tail) ++ Set(elem))
  // head3;tail3;r4;elem4, ((head3 < elem4) ∧ isSorted(Cons(head3, tail3)) ∧ insertSpec(elem4, tail3, r4)) ≺  ⟨ insertSpec(elem4, Cons(head3, tail3), res) ⟩ res 
  def insertV(head: Int, tail: List, r: List, rh: Int, rt: List, elem: Int) = {
    require(head < elem && isSorted(Cons(head, tail)) && content(tail) == content(r) && isSorted(r) && r == Cons(rh, rt) && sortedLemma(head, rh, r))

    //insertSpec(elem, Cons(head, tail), Cons(head, r))
    //rh >= head
    isSorted(Cons(head, r))

  } holds

    //require(head < elem && isSorted(Cons(head, tail)) && isSorted(r) && content(r) == content(tail) ++ Set(elem))
  // head3;tail3;r4;elem4, ((head3 < elem4) ∧ isSorted(Cons(head3, tail3)) ∧ insertSpec(elem4, tail3, r4)) ≺  ⟨ insertSpec(elem4, Cons(head3, tail3), res) ⟩ res 
  def insertV2(head: Int, tail: List, r: List, rh: Int, rt: List, elem: Int) = {
    require(head < elem && isSorted(Cons(head, tail)) && r == insertImpl(elem, tail) && r == Cons(rh, rt))

    //insertSpec(elem, Cons(head, tail), Cons(head, r))
    rh >= head

  } holds

  def insert2(elem : Int, list : List) : List = {
    require(isSorted(list))
    list match {
      case Cons(h, t) =>
        val r = insert2(elem, t)
        if (elem > h) {
          choose { (res : List) => insertSpec(elem, Cons(h,t), res) }
        } else if (elem < h) {
          Cons(elem, Cons(h, t))
        } else {
          Cons(h, t)
        }
      case Nil() =>
        Cons(elem, Nil())
    }
  } ensuring { res => insertSpec(elem, list, res) }

  def insertImpl(elem : Int, list : List) : List = {
    require(isSorted(list))
    list match {
      case Nil() => Cons(elem, Nil())
      case c @ Cons(x, _) if(elem <= x) => Cons(elem, c)
      case Cons(x, xs) => Cons(x, insertImpl(elem, xs))
    }
  } ensuring(insertSpec(elem, list, _))

  /**********************************
   *                                *
   *    M E R G I N G (slow+fast)   *
   *                                *
   **********************************/

  def mergeSpec(list1 : List, list2 : List, res : List) : Boolean = {
    // isSorted(list1) && isSorted(list2) && // Part of precondition, really.
    isSorted(res) && content(res) == content(list1) ++ content(list2)
  }

  // The goal is that the synthesizer figures out that it should use insert.
  // Currently, CEGIS with functions is too slow to handle that benchmark,
  // even when insertImpl is the only function in the scope.
  // (Note that I already propagated the path condition.)
  // If you put mergeImpl in the scope, it solves it (how surprising).
  def merge(list1 : List, list2 : List) : List = {
    require(isSorted(list1) && isSorted(list2))
    choose { (res : List) => mergeSpec(list1, list2, res) }
  }

  def mergeImpl(list1 : List, list2 : List) : List = {
    require(isSorted(list1) && isSorted(list2))

    list1 match {
      case Nil() => list2
      case Cons(x, xs) => insertImpl(x, mergeImpl(xs, list2))
    }
  } ensuring(res => mergeSpec(list1, list2, res))

  def mergeFastImpl(list1 : List, list2 : List) : List = {
    require(isSorted(list1) && isSorted(list2))

    (list1, list2) match {
      case (_, Nil()) => list1
      case (Nil(), _) => list2
      case (Cons(x, xs), Cons(y, ys)) =>
        if(x <= y) {
          Cons(x, mergeFastImpl(xs, list2)) 
        } else {
          Cons(y, mergeFastImpl(list1, ys))
        }
    }
  } ensuring(res => mergeSpec(list1, list2, res))

  /***************************
   *                         *
   *    S P L I T T I N G    *
   *                         *
   ***************************/

  def splitSpec(list : List, res : (List,List)) : Boolean = {
    val s1 = size(res._1)
    val s2 = size(res._2)
    abs(s1 - s2) <= 1 && s1 + s2 == size(list) &&
    content(res._1) ++ content(res._2) == content(list) 
  }

  // I think this one is really close to working. I suspect it would work
  // if the generators in CEGIS had a way to read from tuples. E.g. if
  // t of type (Int,Int) is in context, t._1 and t._2 should be candidates
  // for integers.
  //
  // (Note that if you weaken splitSpec in any way, you get valid and
  // useless answers).
  def split(list : List) : (List,List) = {
    choose { (res : (List,List)) => splitSpec(list, res) }
  }

  def splitImpl(list : List) : (List,List) = (list match {
    case Nil() => (Nil(), Nil())
    case Cons(x, Nil()) => (Cons(x, Nil()), Nil())
    case Cons(x1, Cons(x2, xs)) =>
      val (s1,s2) = splitImpl(xs)
      (Cons(x1, s1), Cons(x2, s2))
  }) ensuring(res => splitSpec(list, res))

  /***********************
   *                     *
   *    S O R T I N G    *
   *                     *
   ***********************/

  def sortSpec(in : List, out : List) : Boolean = {
    content(out) == content(in) && isSorted(out)
  }

  def insertSorted(in: List, v: Int): List = {
    require(isSorted(in));

    in match {
      case Cons(h, t) =>
        val r = insertSorted(t, v)
        if (h < v) {
          Cons(h, r)
        } else if (h > v) {
          Cons(v, Cons(h, t))
        } else {
          Cons(h, t)
        }
      case _ =>
        Cons(v, Nil())
    }
  } ensuring { res => isSorted(res) && content(res) == content(in) ++ Set(v) }

  def insertSorted1(in: List, v: Int): List = {
    require(isSorted(in));

    in match {
      case Cons(h, t) =>
        val r = insertSorted(t, v)
        if (h < v) {
          choose { (res: List) => isSorted(res) && content(res) == content(in) ++ Set(v) }
        } else if (h > v) {
          Cons(v, Cons(h, t))
        } else {
          Cons(h, t)
        }
      case _ =>
        Cons(v, Nil())
    }
  } ensuring { res => isSorted(res) && content(res) == content(in) ++ Set(v) }

  def insertionSortImpl(in : List) : List = (in match {
    case Nil() => Nil()
    case Cons(x, xs) => insertImpl(x, insertionSortImpl(xs))
  }) ensuring(res => sortSpec(in, res))

  // Not really quicksort, neither mergesort.
  def weirdSortImpl(in : List) : List = (in match {
    case Nil() => Nil()
    case Cons(x, Nil()) => Cons(x, Nil())
    case _ =>
      val (s1,s2) = splitImpl(in)
      mergeFastImpl(weirdSortImpl(s1), weirdSortImpl(s2))
  }) ensuring(res => sortSpec(in, res))

  def toLList(list : List) : LList = (list match {
    case Nil() => LNil()
    case Cons(x, xs) => LCons(Cons(x, Nil()), toLList(xs))
  }) ensuring(res => lContent(res) == content(list) && lIsSorted(res))

  def mergeMap(llist : LList) : LList = {
    require(lIsSorted(llist))

    llist match {
      case LNil() => LNil()
      case o @ LCons(x, LNil()) => o
      case LCons(x, LCons(y, ys)) => LCons(mergeFastImpl(x, y), mergeMap(ys))
    }
  } ensuring(res => lContent(res) == lContent(llist) && lIsSorted(res))

  def mergeReduce(llist : LList) : List = {
    require(lIsSorted(llist))

    llist match {
      case LNil() => Nil()
      case LCons(x, LNil()) => x
      case _ => mergeReduce(mergeMap(llist))
    }
  } ensuring(res => content(res) == lContent(llist) && isSorted(res))

  def mergeSortImpl(in : List) : List = {
    mergeReduce(toLList(in))
  } ensuring(res => sortSpec(in, res))
}
