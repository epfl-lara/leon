import cp.Definitions._

object Distinct {
  def main(args: Array[String]) : Unit = {
    val (a, b, c) = choose((i: Int, j: Int, k: Int) => distinct(i, j, k) && 0 < i && 0 < j && 0 < k && i < 3 && j < 3 && k < 5)
    println((a, b, c))
  }
}
