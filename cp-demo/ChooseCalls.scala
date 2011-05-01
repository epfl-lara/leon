import cp.Definitions._

object ChooseCalls {

  def main(args: Array[String]) : Unit = {

    println(
      (((x : Int, y : Int) => 
        2*x + y >= 6 && 
        x + y >= 4 &&
        x >= 0 &&
        y >= 0) minimizing ((x : Int, y : Int) => 3*x + 2*y)
      ).solve
    )

    // println(choose((x : Int, y : Int, z : Int) =>
    //   z == 4*x + 6*y &&
    //   y - x <= 11 &&
    //   x + y <= 27 &&
    //   2*x + 5*y <= 90 &&
    //   x >= 0 &&
    //   y >= 0 maximizing z)
    // )
  }
}
