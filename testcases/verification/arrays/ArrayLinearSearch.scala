import leon.lang._
import leon.collection._
import leon._

object ArrayLinearSearch {

  def existsRec(a: Array[BigInt], x: BigInt, index: Int): Boolean = {
    require(a.length > 0 && index >= 0 && index < a.length &&
            arrayForall(a, 0, index, (el: BigInt) => el != x))

    if(a(index) == x)
      true
    else if(index == a.length - 1)
      false
    else
      existsRec(a, x, index + 1)
    
  } ensuring(found =>
      found || (
        index == a.length - 1 && 
        a(index) != x &&
        arrayForall(a, 0, index, (el: BigInt) => el != x)
      )
    )

  def exists(a: Array[BigInt], x: BigInt): Boolean = {
    require(a.length > 0)
    existsRec(a, x, 0)
  } ensuring(found => found || arrayForall(a, (el: BigInt) => el != x))

}
