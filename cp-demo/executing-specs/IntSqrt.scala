import cp.Definitions._
import cp.Terms._

object IntSqrt {
  def sqrt(i : Int) : Int = {
    ((res: Int) => res > 0 && 
                   res * res <= i  &&
                   (res + 1) * (res + 1) > i).solve
  }

  def main(args: Array[String]): Unit = {
    println("Please provide a positive integer!")
    val i = Console.readInt
    println(sqrt(i))
  }
 
}
