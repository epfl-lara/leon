object Test {
  def main(args: Array[String]): Unit = {

    println("Ok")
  }

  def useless(i: Int, j: Int): Int = {
    require(i == j)
    i + j
  } ensuring(res => res == 2 * i)

  def booleans: Unit = {
    var b : Boolean = true
    b = false
  
  }
}
