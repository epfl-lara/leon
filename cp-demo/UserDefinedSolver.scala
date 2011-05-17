import cp.Definitions._
import cp.Terms._

@spec object Specs {
  sealed abstract class List
  case class Cons(head : Int, tail : List) extends List
  case class Nil() extends List
}
object UserDefinedSolver {
  import Specs._

  def main(args: Array[String]): Unit = {
    val myEnumerator = Iterator[List](Nil(), Cons(42, Nil()))
    val userDefined = customSolver(myEnumerator)

    for (l <- userDefined.findAll) {
      println("Here is a solution: " + l)
    }

    userDefined.solve
  }
}
