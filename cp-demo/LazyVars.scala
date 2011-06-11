import cp.Terms._
import cp.Definitions._
import cp.LTrees._

object LazyVars {
  def NonnegativeInt = ((x: Int) => x >= 0).lazyFindAll
  def chooseInt(lower: Int, upper: Int) = ((x: Int) => x >= lower && x <= upper).lazyFindAll

  def main(args: Array[String]): Unit = {
    // for {
    //   x <- chooseInt(0, 5)
    //   y <- chooseInt(1, 3)
    //   if x > y
    // } {
    //   val a: Int = x
    //   val b: Int = y
    //   println(a, b)
    // }

    println("...")

    for {
      x <- NonnegativeInt
      if x < 3
      y <- NonnegativeInt // replace these with Stream.from(0) and the code will loop forever without printing anything
      if x > y
    } {
      val i: Int = x
      val j: Int = y
      println(i, j)
    }
  }
}
