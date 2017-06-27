import leon.annotation._
import leon.annotation.grammar._
import leon.grammar.Grammar._
import leon.lang._
import leon.lang.synthesis._
import leon.collection._

object SortedListInsertionSort {

  def isSorted(list: List[BigInt]): Boolean = list match {
    case Cons(x1, t@Cons(x2, _)) => x1 <= x2 && isSorted(t)
    case _ => true
  }

  def insert(in: List[BigInt], v: BigInt): List[BigInt] = {
    require(isSorted(in))
    in match {
      case Cons(h, t) =>
        if (v < h) {
          Cons(v, in)
        } else if (v == h) {
          in
        } else {
          Cons(h, insert(t, v))
        }
      case Nil() =>
        Cons(v, Nil())
    }
  } ensuring { res =>
    (res.content == in.content ++ Set(v)) && isSorted(res)
  }

  @production(50) def useIns(in: List[BigInt], v: BigInt): List[BigInt] = insert(in, v)

  def insertionSort(in: List[BigInt]): List[BigInt] = {
    choose { (out: List[BigInt]) =>
      out.content == in.content && isSorted(out)
    }
  }
}
