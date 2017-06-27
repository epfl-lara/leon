import leon.annotation._
import leon.annotation.grammar._
import leon.grammar.Grammar._
import leon.lang._
import leon.lang.synthesis._
import leon.collection._

object StrictSortedListUnion {

  def isSorted(list: List[BigInt]): Boolean = list match {
    case Cons(x1, t@Cons(x2, _)) => x1 < x2 && isSorted(t)
    case _ => true
  }

  def insert(in1: List[BigInt], v: BigInt): List[BigInt] = {
    require(isSorted(in1))
    in1 match {
      case Cons(h, t) =>
        if (v < h) {
          Cons(v, in1)
        } else if (v == h) {
          in1
        } else {
          Cons(h, insert(t, v))
        }
      case Nil() =>
        Cons(v, Nil())
    }

  } ensuring { res =>
    (res.content == in1.content ++ Set(v)) && isSorted(res)
  }

  @production(50) def useInsert(in1: List[BigInt], v: BigInt): List[BigInt] = insert(in1, v)

  def union(in1: List[BigInt], in2: List[BigInt]) = {
    require(isSorted(in1) && isSorted(in2))
    choose { (out : List[BigInt]) =>
      (out.content == in1.content ++ in2.content) && isSorted(out)
    }
  }
}
