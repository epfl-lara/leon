import cp.Definitions._
import cp.Terms._

object Assuming {
  def assuming(c: Constraint0)(block: => Unit) : Unit = {
    for (u <- c.lazyFindAll) {
      block
    }
  }

  def main(args: Array[String]): Unit = {
    for (x <- ((x: Int) => x >= 0 && x < 4).lazyFindAll) {
      assuming(() => x <= 1) {
        println("hey!")
      }
      assuming(() => x > 1) {
        println("ho!")
      }
    }
  }
}
