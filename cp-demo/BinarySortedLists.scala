import cp.Definitions._
import cp.Terms._

object BinarySortedLists {
  def main(args : Array[String]) : Unit = {
    val inRange : Constraint1[Int] = ((x : Int) => x >= 0 && x <= 1)
  
    val sortedLists =
      for(x <- inRange.lazyFindAll;
        y <- inRange.lazyFindAll if y >= x;
        z <- inRange.lazyFindAll if z >= y)
      yield {
        x.value; y.value; z.value;  
        List(x, y, z)
      }
  
    sortedLists.foreach(println(_))
  }
}
