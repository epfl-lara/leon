import cp.Definitions._
import cp.Terms._
import cp.LTrees._

object LazyNQueens {
  def main(args: Array[String]): Unit = {
    val numCols = 8

    val cols = new Array[L[Int]](numCols)

    for (i <- 0 until numCols) {
      // bounds
      var c: Constraint1[Int] = ((x: Int) => x >= 0 && x < numCols)

      // different from previous
      for (j <- 0 until i) {
        c = c && ((x: Int) => x != cols(j))
      }

      // not on a same diagonal as previous
      for (j <- 0 until i) {
        c = c && ((x: Int) => x - cols(j) != i - j && x - cols(j) != j - i)
      }

      cols(i) = c.lazySolve
    }

    for (c <- cols)
      println(c.value)
  }
}
