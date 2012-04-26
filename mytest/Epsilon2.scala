import leon.Utils._

object Epsilon1 {

  def rand(): Int = epsilon((x: Int) => true)
  def rand2(x: Int): Int = epsilon((y: Int) => true)
  def rand3(x: Int): Int = epsilon((y: Int) => x == x)

  //this should hold, that is the expected semantic of our epsilon
  def property1(): Boolean = {
    rand() == rand() 
  } holds

  //this should hold, that is the expected semantic of our epsilon
  def property2(x: Int): Boolean = {
    rand2(x) == rand2(x+1) 
  } holds

  //this should NOT hold
  def property3(x: Int): Boolean = {
    rand3(x) == rand3(x+1)
  } holds
}
