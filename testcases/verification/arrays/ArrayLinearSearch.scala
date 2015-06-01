import leon.lang._
import leon.collection._
import leon._

object ArrayLinearSearch {

  def existsRec(a: Array[BigInt], x: BigInt, index: Int): Int = {
    require(
      a.length > 0 && index >= 0 && index < a.length)
      //arrayForall(a, 0, index, (el: BigInt) => el != x))

    if(a(index) == x)
      index
    else if(index >= a.length - 1)
      -1
    else
      existsRec(a, x, index+1)
    
  } ensuring(pos => {
      if(pos == -1)
        arrayForall(a, index, a.length, (el: BigInt) => el != x)
      else
        pos >= index && 
        pos < a.length &&
        a(pos) == x
  })
        

      //arrayForall(a, 0, pos, (el: BigInt) => el != x) &&
      //(if(a(index) == x) {
      //  arrayForall(a, 0, pos, (el: BigInt) => el != x) &&
      //  a(index) == x &&
      //  index == pos
      //} else if(index >= a.length - 1) {
      //  index == a.length - 1 &&
      //  pos == a.length &&
      //  arrayForall(a, 0, pos, (el: BigInt) => el != x) &&
      //  a(a.length - 1) != x
      //} else {
      //  arrayForall(a, 0, index+1, (el: BigInt) => el != x) &&
      //  arrayForall(a, 0, pos, (el: BigInt) => el != x)
        //pos == existsRec(a, x, index+1) &&
        //index < a.length - 1 &&
        //a(index) != x &&
        //pos == existsRec(a, x, index+1) &&
        //(if(a(index+1) == x)
        //  arrayForall(a, 0, index+1, (el: BigInt) => el != x) &&
        //  index+1 == pos &&
        //  arrayForall(a, 0, pos, (el: BigInt) => el != x)
        // else if(index+1 >= a.length-1)
        //  arrayForall(a, 0, a.length, (el: BigInt) => el != x) &&
        //  pos == a.length &&
        //  arrayForall(a, 0, pos, (el: BigInt) => el != x)
        // else 
        //  arrayForall(a, 0, pos, (el: BigInt) => el != x)
        //)
      //})
      

  def exists(a: Array[BigInt], x: BigInt): Int = {
    require(a.length > 0)
    existsRec(a, x, 0)
  } ensuring(index => {
    if(index == -1)
      arrayForall(a, (el: BigInt) => el != x)
    else
      a(index) == x
  })


}
