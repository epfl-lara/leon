import leon.lang._
import leon.lang.synthesis._
import leon.annotation._
object TwoSort {
/*
  def sort2(x : BigInt, y : BigInt) = choose{(res: (BigInt,BigInt)) =>
    Set(x,y) == Set(res._1, res._2) && res._1 <= res._2
  }
*/

/*
  def sort2(x : BigInt, y : BigInt) = {
    ???[(BigInt, BigInt)]
  } ensuring{(res: (BigInt,BigInt)) =>
    Set(x,y) == Set(res._1, res._2) && res._1 <= res._2
  }
*/


// def testSort2 = sort2(30, 4)

/*
  def sort2(x: BigInt, y: BigInt) = choose{(res: (BigInt,BigInt)) => 
    sort2spec(x,y,res)
  }

  def sort2spec(x: BigInt, y: BigInt, res: (BigInt, BigInt)): Boolean = {
    Set(x,y) == Set(res._1, res._2) && res._1 <= res._2
  }

  def unique2(x: BigInt, y: BigInt,
              res1: (BigInt, BigInt),
              res2: (BigInt, BigInt)): Boolean = {
    require(sort2spec(x,y,res1) && sort2spec(x,y,res2))
    res1 == res2
  } holds
 */

/*
  def sort3spec(x: BigInt, y: BigInt, z: BigInt, res: (BigInt,BigInt,BigInt)): Boolean = {
    Set(x,y,z) == Set(res._1, res._2, res._3) && 
    res._1 <= res._2 && res._2 <= res._3
  }

  def unique3(x: BigInt, y: BigInt, z: BigInt,
         res1: (BigInt,BigInt,BigInt),
         res2: (BigInt,BigInt,BigInt)): Boolean = {
    require(sort3spec(x,y,z,res1) && sort3spec(x,y,z,res2))
    res1 == res2
  }.holds
 */
}
