import leon.lang._
import leon.collection._
import leon._

object ArrayLinearSearch {

  def exists(a: Array[BigInt], x: BigInt): Boolean = {
    require(a.length > 0)

    var i = 0
    var found = false
    (while(!found && i < a.length) {
      if(a(i) == x)
        found = true
      i += 1
    }) invariant(
         i >= 0 && i <= a.length && (
         if(found)
           arrayExists(a, 0, i, (y: BigInt) => y == x)
         else true)
       )
    found

  } ensuring(res => {
      if(res)
        arrayExists(a, (y: BigInt) => y == x)
      else
        true
    })

}
