import leon.lang._
import leon.collection._
import leon._

object ArrayLinearSearch {

  def existsRec(a: Map[BigInt, BigInt], length: BigInt, x: BigInt, index: BigInt): BigInt = {
    require(
      length > 0 && index >= 0 && index < length &&
      boundedForall(0, index, (i: BigInt) => a(i) != x))

    if(a(index) == x)
      index
    else if(index >= length - 1)
      length
    else
      existsRec(a, length, x, index+1)
    
  } ensuring(pos => {
      //arrayForall(a, 0, pos, (el: BigInt) => el != x)

      //arrayForall(a, 0, pos, (el: BigInt) => el != x) &&
      (if(a(index) == x) {
        boundedForall(0, pos, (i: BigInt) => a(i) != x) &&
        a(index) == x &&
        index == pos
      } else if(index >= length - 1) {
        index == length - 1 &&
        pos == length &&
        boundedForall(0, pos, (i: BigInt) => a(i) != x) &&
        a(length - 1) != x
      } else {
        boundedForall(0, index+1, (i: BigInt) => a(i) != x) &&
        boundedForall(0, pos, (i: BigInt) => a(i) != x)
        //pos == existsRec(a, x, index+1) &&
        //index < length - 1 &&
        //a(index) != x &&
        //pos == existsRec(a, x, index+1) &&
        //(if(a(index+1) == x)
        //  arrayForall(a, 0, index+1, (el: BigInt) => el != x) &&
        //  index+1 == pos &&
        //  arrayForall(a, 0, pos, (el: BigInt) => el != x)
        // else if(index+1 >= length-1)
        //  arrayForall(a, 0, length, (el: BigInt) => el != x) &&
        //  pos == length &&
        //  arrayForall(a, 0, pos, (el: BigInt) => el != x)
        // else 
        //  arrayForall(a, 0, pos, (el: BigInt) => el != x)
        //)
      })
    })
      

  //def exists(a: Array[BigInt], x: BigInt): Int = {
  //  require(a.length > 0)
  //  existsRec(a, x, 0)
  //} ensuring(index => arrayForall(a, 0, index, (el: BigInt) => el != x))

}
