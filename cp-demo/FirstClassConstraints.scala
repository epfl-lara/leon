import cp.Definitions._
import cp.Terms._

@spec object Specs {
  abstract class MyList
  case class MyCons(head : Int, tail : MyList) extends MyList
  case class MyNil() extends MyList
}

object FirstClassConstraints {
  import Specs._

  def oneOf(lst : List[Int]) : Constraint1[Int] = lst match {
   case Nil => (x : Int) => false
   case c::cs => ((x : Int) => x == c) || oneOf(cs)
  }

  def main(args: Array[String]) : Unit = {
    val l = List(1, 3, 5, 7)

    for (x <- (oneOf(l) minimizing (- (_: Int))).findAll)
      println("A solution: " + x)

    val mapper : Term1[MyList,MyList] = (l : MyList) => l match { case MyCons(_, xs) => xs; case x => x }

  }
}
