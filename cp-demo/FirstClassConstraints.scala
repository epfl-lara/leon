import cp.Definitions._
import cp.Constraints._

object FirstClassConstraints {
  def oneOf(lst : List[Int]) : Constraint1[Int] = lst match {
   case Nil => (x : Int) => false
   case c::cs => ((x : Int) => x == c) || oneOf(cs)
  }

  def main(args: Array[String]) : Unit = {
    val l = List(1, 3, 5, 7)

    for (x <- (oneOf(l) minimizing ((x: Int) => x)).findAll)
      println("A solution: " + x)

    // val p = ((x : Int, y : Int) => x > y).proj0 && ((x : Int, y : Int) => x < y).proj0
    // println(p.solve)

  }
}
