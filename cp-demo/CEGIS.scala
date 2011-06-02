import cp.Definitions._
import cp.Terms._

object CEGIS {
  def main(args: Array[String]): Unit = {
    var continue = true

    val initialX = ((x: Int) => true).solve
    println("Initial x: " + initialX)

    def cnstrGivenX(x0: Int)              : Constraint2[Int,Int] = ((a: Int, b: Int) => a * (x0 - 1) < b * x0)
    def cnstrGivenParams(a0: Int, b0: Int): Constraint1[Int] = ((x: Int) => a0 * (x - 1) < b0 * x)

    var currentCnstr = cnstrGivenX(initialX)

    while (continue) {
      currentCnstr.find match {
        case Some((a, b)) => {
          println("found candidate parameters a = " + a + ", b = " + b)
          (! cnstrGivenParams(a, b)).find match {
            case None => 
              println("proved!")
              continue = false
            case Some(counterex) => 
              println("found a counterexample for x: " + counterex)
              currentCnstr = currentCnstr && cnstrGivenX(counterex)
          }
        }
        case None => 
          println("cannot prove property!")
          continue = false
      }
    }
  }
}
