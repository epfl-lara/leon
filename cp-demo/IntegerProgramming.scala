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
  }
}
