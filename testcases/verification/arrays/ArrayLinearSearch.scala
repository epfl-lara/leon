import leon.lang._
import leon.collection._
import leon._

object ArrayLinearSearch {

  def existsRec(a: Array[BigInt], x: BigInt, index: Int, found: Boolean): Boolean = {
    require(a.length > 0 && a.length < 10 && index >= 0 && index <= a.length &&
            (found || arrayForall(a, 0, index, (el: BigInt) => el != x)))

    if(index >= a.length)
      found
    else {
      if(a(index) != x)
        true
      else
        existsRec(a, x, index + 1, found)
    }
  } ensuring(found =>
      found || arrayForall(a, 0, index, (el: BigInt) => el != x)
    )

}
