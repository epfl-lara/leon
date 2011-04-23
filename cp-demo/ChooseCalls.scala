import cp.Definitions._

object ChooseCalls {

  def main(args: Array[String]) : Unit = {

    println(choose((x : Int, y : Int, w : Int) => 
      w == 3*x + 2*y && 
      2*x + y >= 6 && 
      x + y >= 4 &&
      x >= 0 &&
      y >= 0 minimizing w)
    )

    println(choose((x : Int, y : Int, z : Int) =>
      z == 4*x + 6*y &&
      y - x <= 11 &&
      x + y <= 27 &&
      2*x + 5*y <= 90 &&
      x >= 0 &&
      y >= 0 maximizing z)
    )

    val (a, b, c) = choose((i: Int, j: Int, k: Int) => distinct(i, j, k) && 0 < i && 0 < j && 0 < k && i < 3 && j < 3 && k < 5)
    println((a, b, c))
  }
}
