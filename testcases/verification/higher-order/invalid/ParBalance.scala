import leon.lang._
import leon.collection._

object ParBalance {

  sealed abstract class List
  case class Cons(head: BigInt, tail: List) extends List
  case class Nil() extends List

  sealed abstract class Option
  case class Some(x: BigInt) extends Option
  case class None() extends Option

  val openPar : BigInt = BigInt(1)
  val closePar : BigInt = BigInt(2)

  def balanced(list: List, counter: BigInt): Boolean = {
    if (counter < 0) false else list match {
      case Cons(head, tail) =>
        val c = if (head == openPar) counter + 1
          else if (head == closePar) counter - 1
          else counter
        balanced(tail, c)
      case Nil() => counter == 0
    }
  }

  def balanced_nonEarly(list: List, counter: BigInt): Boolean = {
    list match {
      case Cons(head, tail) =>
        if (counter < 0) balanced_nonEarly(tail, counter) else {
          val c = if (head == openPar) counter + 1
            else if (head == closePar) counter - 1
            else counter
          balanced_nonEarly(tail, c)
        }
      case Nil() => counter == 0
    }
  } ensuring { res => res == balanced(list, counter) }

  def balanced_withFailure(list: List, counter: BigInt, failed: Boolean): Boolean = {
    require(counter >= 0 || failed)
    list match {
      case Cons(head, tail) =>
        val c = if (head == openPar) counter + 1
          else if (head == closePar) counter - 1
          else counter
        balanced_withFailure(tail, c, failed || c < 0)
      case Nil() => !failed && counter == 0
    }
  } ensuring { res =>
    if (failed) {
      res == balanced_nonEarly(list, -1)
    } else {
      res == balanced_nonEarly(list, counter)
    }
  }

  def balanced_withReduce(list: List, p: (BigInt, BigInt)): Boolean = {
    require(p._1 >= 0 && p._2 >= 0)
    list match {
      case Cons(head, tail) =>
        val p2 = reduce(p, parPair(head))
        balanced_withReduce(tail, p2)
      case Nil() =>
        p._1 == 0 && p._2 == 0
    }
  } ensuring { res => res == balanced_withFailure(list, p._1 - p._2, p._2 > 0) }

  def balanced_foldLeft_equivalence(list: List, p: (BigInt, BigInt)): Boolean = {
    require(p._1 >= 0 && p._2 >= 0)
    val f = (s: (BigInt, BigInt), x: BigInt) => reduce(s, parPair(x))
    (foldLeft(list, p, f) == (BigInt(0), BigInt(0))) == balanced_withReduce(list, p) && (list match {
      case Cons(head, tail) =>
        val p2 = f(p, head)
        balanced_foldLeft_equivalence(tail, p2)
      case Nil() => true
    })
  }.holds

  def foldRight[A](list: List, state: A, f: (BigInt, A) => A): A = list match {
    case Cons(head, tail) =>
      val tailState = foldRight(tail, state, f)
      f(head, tailState)
    case Nil() => state
  }

  def foldLeft[A](list: List, state: A, f: (A, BigInt) => A): A = list match {
    case Cons(head, tail) =>
      val nextState = f(state, head)
      foldLeft(tail, nextState, f)
    case Nil() => state
  }

  def reduce(p1: (BigInt, BigInt), p2: (BigInt, BigInt)): (BigInt, BigInt) = {
    if (p1._1 >= p2._2) {
      (p1._1 - p2._2 + p2._1, p1._2)
    } else {
      (p2._1, p2._2 - p1._1 + p1._2)
    }
  }

  def reduce_associative(p1: (BigInt, BigInt), p2: (BigInt, BigInt), p3: (BigInt, BigInt)): Boolean = {
    reduce(p1, reduce(p2, p3)) == reduce(reduce(p1, p2), p3)
  }.holds

  def swap(p: (BigInt, BigInt)): (BigInt, BigInt) = (p._2, p._1)

  def reduce_inverse(p1: (BigInt, BigInt), p2: (BigInt, BigInt)): Boolean = {
    reduce(p1, p2) == swap(reduce(swap(p2), swap(p1)))
  }.holds

  def reduce_associative_inverse(p1: (BigInt, BigInt), p2: (BigInt, BigInt), p3: (BigInt, BigInt)): Boolean = {
    reduce(p1, reduce(p2, p3)) == swap(reduce(reduce(swap(p3), swap(p2)), swap(p1)))
  }.holds

  def reduce_associative_inverse2(p1: (BigInt, BigInt), p2: (BigInt, BigInt), p3: (BigInt, BigInt)): Boolean = {
    reduce(reduce(p1, p2), p3) == swap(reduce(swap(p3), reduce(swap(p2), swap(p1))))
  }.holds

  def parPair(x: BigInt): (BigInt, BigInt) = {
    if (x == openPar) (1, 0) else if (x == closePar) (0, 1) else (0, 0)
  }

  def fold_equivalence(list: List): Boolean = {
    val s = (BigInt(0), BigInt(0))
    val fl = (s: (BigInt, BigInt), x: BigInt) => reduce(s, parPair(x))
    val fr = (x: BigInt, s: (BigInt, BigInt)) => reduce(swap(parPair(x)), s)

    foldLeft(list, s, fl) == swap(foldRight(list, swap(s), fr))
  }.holds

}
