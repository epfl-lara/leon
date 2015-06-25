import leon.lang.synthesis._
import leon.annotation._
object Max {
  def max(x: Int, y: Int): Int = {
    val d = x - y
    if (d > 0) x
    else y
  }
  // ensuring(res => (res == x || res == y))
  //  x <= res && y <= res

  def test1 = max(10, 5)
  def test2 = max(-5, 5)
  def test3 = max(-5, -7)

  //def test4 = max(-1639624704, 1879048192)

/*
  def max(x: BigInt, y: BigInt): BigInt = {
    val d = x - y
    if (d > 0) x
    else y
   } ensuring(res =>
     x <= res && y <= res && (res == x || res == y))
  */

/*
  def rmax(x: BigInt, y: BigInt) =
    if (x <= y) x else y

  def max(x: BigInt, y: BigInt): BigInt = {
    val d = x - y
    if (d > 0) x
    else y
  } ensuring(res =>  res==rmax(x,y))
*/

/*
  def max_lemma(x: BigInt, y: BigInt, z: BigInt): Boolean = {
    max(x,x) == x &&
    max(x,y) == max(y,x) &&
    max(x,max(y,z)) == max(max(x,y), z) &&
    max(x,y) + z == max(x + z, y + z)
  } ensuring(_ == true)
  // holds
*/

/*
  def max(x: Int, y: Int): Int = {
    require(0 <= x && 0 <= y)
    val d = x - y
    if (d > 0) x
    else y
  } ensuring (res =>
    x <= res && y <= res && (res == x || res == y))
*/

/*
  def max(x: BigInt, y: BigInt): BigInt = {
    ???[BigInt]
  } ensuring(res => (res == x || res == y) &&  x <= res && y <= res)
*/
}
