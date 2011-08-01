import cp.Definitions._
import cp.Terms._

object Product {
  def main(args: Array[String]): Unit = {
    val c1 = ((x: Int) => x > 5).c
    val c2 = ((x: Int) => x > 41).c
    val c22 = ((x: Int, y: Int, z: Int) => x > y).c

    val c3 = c1 product c2
    val c32 = c1 product c22

    val c4 = ((a: Boolean, b: Int) => a == b > 0).c
    val c5 = ((i: Int, j: Int) => i > j).c

    val c6 = c4 product c5

    println(c3.solve)
    println(c32.solve)
    println(c6.solve)
  }
}
