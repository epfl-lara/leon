import cp.Definitions._
import cp.Terms._

object SatSolver extends App {
  val problem : List[List[Int]] = List(
    List(-1, 2, 3),
    List(1, -2),
    List(4)
  )

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
