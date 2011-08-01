import cp.Definitions._
import cp.Terms._

object Product {
  def main(args: Array[String]): Unit = {
    val c1 = ((x: Int) => x > 5).c
    val c2 = ((x: Int) => x > 41).c

    val c3 = c1 product1 c2
    println(c3.solve)
  }
}
