import cp.Definitions._
import cp.Terms._

object Product {
  def main(args: Array[String]): Unit = {
    val c1 = ((x: Int) => x > 5).c
    val c2 = ((x: Int) => x > 41).c

    val c3 = c1 product1 c2

    val c4 = ((a: Boolean, b: Int) => a == b > 0).c
    val c5 = ((i: Int, j: Int) => i > j).c

    val c6 = c4 product2 c5

    println(c3.solve)
    println(c6.solve)
  }
}
