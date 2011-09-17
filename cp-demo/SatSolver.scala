import cp.Definitions._
import cp.Terms._
import scala.io.Source

object SatSolver {
  val defaultProblem : List[List[Int]] = List(
    List(-1, 2, 3),
    List(1, -2),
    List(4)
  )

  def main(args: Array[String]): Unit = {

    val problem: List[List[Int]] = if (args.length > 0 ) (for (line <- Source.fromFile(args(0)).getLines if (!line.startsWith("c") && !line.startsWith("p"))) yield {
        line.split(" ").toList.map(_.toInt)
    }).toList else defaultProblem

    type CM = Constraint1[Map[Int,Boolean]]
    val solution : CM =
      problem.foldLeft[CM]((m:Map[Int,Boolean]) => true)((cons:CM,clause:List[Int]) => cons && clause.foldLeft[CM]((m:Map[Int,Boolean]) => false)((cons:CM,lit:Int) => {
            val isPos = lit > 0
            val abs = scala.math.abs(lit)
            cons || ((m:Map[Int,Boolean]) => m(abs) == isPos)
          }))

    val answer = solution.solve
    println("Solution map : " + answer)
    (1 to 4).foreach(i => println("i : " + answer(i)))
  }
}
