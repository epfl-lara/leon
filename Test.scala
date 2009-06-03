object Test {
  def main(args: Array[String]): Unit = {
    require(2 == 2)

    println("Ok")
  } ensuring (res => 2 == 2)
}
