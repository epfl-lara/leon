import leon.Utils._

object Even {

  //def getEven: Int = {
  //  val e = epsilon((i: Int) => true)
  //  e + e
  //}) ensuring(isEven(_))

  def double(i: Int): Int = (2*i) ensuring (isEven(_))

  def isEven(i: Int): Boolean = i % 2 == 0

}
