import cp.Definitions._
import cp.Constraints._

object FirstClassConstraints {
  def oneOf(lst : List[Int]) : Constraint1[Int] = lst match {
   case Nil => (x : Int) => false
   case c::cs => ((x : Int) => x == c) || oneOf(cs)
  }

  @spec object Specs {
    abstract class A
    case class B() extends A
    case class C() extends A
  }

  def main(args: Array[String]) : Unit = {
    val outer: Int = 42
    val pred1 : Constraint1[Int] = (x : Int) => x > outer && x < 50
    val pred2 : Constraint1[Int] = (y : Int) => y == outer
    val orPred = pred1 || pred2

    val solution: Int = (!orPred).solve

    val optSol = orPred.find

    val minSol = orPred minimizing ((x: Int) => x)

    println("min sol: " + minSol.solve)

    println(solution)
    println(optSol)

    for (s <- orPred.findAll)
      println("A solution : " + s)

    val twoArgPred : Constraint2[Int, Boolean] = (x : Int, b : Boolean) => x > 42 && !b

    println(twoArgPred.solve)
  }
}
