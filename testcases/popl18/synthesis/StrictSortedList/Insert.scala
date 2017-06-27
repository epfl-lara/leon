import leon.annotation._
import leon.annotation.grammar._
import leon.grammar.Grammar._
import leon.lang._
import leon.lang.synthesis._
import leon.collection._

object StrictSortedListInsert {
 
  def isSorted(list: List[BigInt]): Boolean = list match {
    case Cons(x1, t@Cons(x2, _)) => x1 < x2 && isSorted(t)
    case _ => true
  }

  def insert(in: List[BigInt], v: BigInt): List[BigInt] = {
    require(isSorted(in))

    choose { (out : List[BigInt]) =>
      (out.content == in.content ++ Set(v)) && isSorted(out)
    }
  }
}
