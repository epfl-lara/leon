import cp.Definitions._
import cp.Terms._

object NQueens {
  def conjoin[T](cs: Constraint1[T]*): Constraint1[T] = {
    cs.reduceLeft[Constraint1[T]]{ case (acc, c) => acc && c }
  }

  def main(args: Array[String]): Unit = {
    val numCols = 8

    var cnstr: Constraint1[Map[Int,Int]] = ((cols: Map[Int,Int]) => true)

    /* All queens are on different columns */
    for (i <- 0 until numCols; j <- (i + 1) until numCols) {
      cnstr &&= ((cols: Map[Int,Int]) => cols(i) != cols(j))
    }

    /* Columns are within the bounds */
    for (i <- 0 until numCols) {
      cnstr &&= ((cols: Map[Int,Int]) => cols(i) >= 0 && cols(i) < numCols)
    }

    /* No two queens are on same diagonal */
    for (i <- 0 until numCols; j <- 0 until i) {
      cnstr &&= ((cols: Map[Int,Int]) => cols(i) - cols(j) != i - j && cols(i) - cols(j) != j - i)
    }

    println(cnstr.solve.map{ case (k, v) => "Place queen " + k + " on column " + v }.mkString("\n"))
  }
}
