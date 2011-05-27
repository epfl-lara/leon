import cp.Definitions._
import cp.Terms._

@spec object Specs {
  abstract class List
  case class Cons(head : Int, tail : List) extends List
  case class Nil() extends List

  def size(l: List) : Int = (l match {
      case Nil() => 0
      case Cons(_, t) => 1 + size(t)
  }) ensuring(res => res >= 0)
}

object FirstClassConstraints {
  import Specs._

  def oneOf(lst : Seq[Int]) : Constraint1[Int] = lst match {
   case Seq() => (x : Int) => false
   case Seq(c, cs @ _*) => ((x : Int) => x == c) || oneOf(cs)
  }

  
  def hasSize(size : Int) : Constraint1[List] = {
    if (size <= 0)
      (l : List) => l == Nil()
    else {
      ((l : List) => l != Nil()) && hasSize(size - 1).compose0((l : List) => l match { case Cons(_,xs) => xs ; case x => x } )
    }
  }

  def main(args: Array[String]) : Unit = {
    val l = Seq(1, 3, 5, 7)

    for (x <- oneOf(l).findAll)
      println("A solution to `oneOf': " + x)

    val nilHasSize3 = hasSize(3)(Nil())
    println("Does Nil() have size 3? : " + nilHasSize3)
 
    val aList = hasSize(5).solve
    println("A list of size 5: " + aList)
  }
}
