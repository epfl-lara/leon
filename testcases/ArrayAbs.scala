import leon.Utils._

object Test {

  def isPos(array: Array[Int], index: Int, to: Int): Boolean = {
    require(index >= 0)
    if(index >= to || index >= array.length)
      true
    else
      array(index) >= 0 && isPos(array, index+1, to)
  }

  //def abs(array: Array[Int], index: Int): Array[Int] = {
  //  require(index >= 0 && isPos(array, 0, index))
  //  if(index >= array.length) array else {
  //    val el = array(index)
  //    val newEl = if(el < 0) -el else el
  //    abs(array.updated(index, newEl), index+1)
  //  }
  //} ensuring(res => isPos(res, 0, index+1))

  def abs(array: Array[Int], index: Int): Array[Int] = {
    require(index >= 0 && isPos(array, 0, index))
    if(index >= array.length) array else {
      abs(array.updated(index, 0), index+1)
    }
  } ensuring(res => isPos(res, 0, index+1))

}
