import cp.Definitions._

object Assuming {
  def main(args: Array[String]): Unit = {
    for (x <- ((x: Int) => x >= 0 && x < 4).lazyFindAll) {
      for (b <- ((b: Boolean) => b && x <= 1).lazyFindAll) {
        println("hey!")
      }
      for (b <- ((b: Boolean) => b && x > 1).lazyFindAll) {
        println("ho!")
      }
    }
  }
}
