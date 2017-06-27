import leon.annotation._
import leon.annotation.grammar._
import leon.grammar.Grammar._
import leon.lang._
import leon.lang.synthesis._
import leon.collection._

object SortedListDiff {

  def isSorted(list: List[BigInt]): Boolean = list match {
    case Cons(x1, t@Cons(x2, _)) => x1 <= x2 && isSorted(t)
    case _ => true
  }

  def delete(in1: List[BigInt], v: BigInt): List[BigInt] = {
    require(isSorted(in1))
    in1 match {
      case Cons(h,t) =>
        if (h < v) {
          Cons(h, delete(t, v))
        } else if (h == v) {
          delete(t, v)
        } else {
          in1
        }
      case Nil() =>
        Nil[BigInt]()
    }
  } ensuring { res =>
    res.content == in1.content -- Set(v) && isSorted(res)
  }

  @production(50) def useD(in1: List[BigInt], v: BigInt): List[BigInt] = delete(in1, v)

  def diff(in1: List[BigInt], in2: List[BigInt]) = {
    require(isSorted(in1) && isSorted(in2))

    choose { (out : List[BigInt]) =>
      (out.content == in1.content -- in2.content) && isSorted(out)
    }
  }

}
