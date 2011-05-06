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

  
  def hasSize(size : Int) : Constraint1[MyList] = {
    if (size <= 0)
      (l : MyList) => l == MyNil()
    else {
      ((l : MyList) => l != MyNil()) && hasSize(size - 1).compose0((l : MyList) => l match { case MyCons(_,xs) => xs ; case x => x } )
    }
  }

  def main(args: Array[String]) : Unit = {
    val l = List(1, 3, 5, 7)

    for (x <- (oneOf(l) minimizing (- (_: Int))).findAll)
      println("A solution: " + x)

    val f1 : Term1[Int,Int] = (x: Int) => x + 1
    val f2 : Term1[Int,Int] = (x: Int) => x * 2
    val f3 = f2 compose0 f1
    val f4 = f2 compose0 ((x : Int, y : Int) => x + y)
    println("Composed f3: " + f3.expr)
    println("Composed f4: " + f4.expr)

    val f5 = ((x : Int, y : Int) => x + y) compose0 ((x : Int) => x + 42) 
    println("Composed f5: " + f5.expr)
    val f6 = f5 compose1 ((x: Int) => x + 43)
    println("Composed f6: " + f6.expr)

    println("has size 3: " + hasSize(3).expr)
  }
}
