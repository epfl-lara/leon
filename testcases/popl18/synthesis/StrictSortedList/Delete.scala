import leon.annotation._
import leon.annotation.grammar._
import leon.grammar.Grammar._
import leon.lang._
import leon.lang.synthesis._
import leon.collection._

object StrictSortedListDelete {

  def isSorted(list: List[BigInt]): Boolean = list match {
    case Cons(x1, t@Cons(x2, _)) => x1 < x2 && isSorted(t)
    case _ => true
  }

  def delete(in: List[BigInt], v: BigInt) = {
    require(isSorted(in))

    choose( (res : List[BigInt]) =>
      (res.content == in.content -- Set(v)) && isSorted(res)
    )
  }

}
