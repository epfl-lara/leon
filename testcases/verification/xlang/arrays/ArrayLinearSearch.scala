import leon.lang._
import leon.collection._
import leon._

object ArrayLinearSearch {

  def exists(a: Array[BigInt], x: BigInt): Int = {
    require(a.length > 0)

    var indexElement = -1
    var i = 0
    var found = false
    (while(!found && i < a.length) {
      if(a(i) == x)
        found = true
      i += 1
    }) invariant(
         i >= 0 && i <= a.length && (
           if(indexElement == -1)
             arrayForall(a, 0, i, (el: BigInt) => el != x)
           else {
             indexElement >= 0 && indexElement <= i &&
             a(indexElement) == x
           }
         )
       )
    indexElement

  } ensuring(res => {
      if(res == -1)
        arrayForall(a, (y: BigInt) => y != x)
      else
        a(res) == x
    })

}
