import cp.Definitions._
import cp.Terms._

object CEGISsqr {
  @spec def sqr(x: Int, y: Int): Boolean = {
    x*x <= y && (x+1)*(x+1) > y
  }

  @spec def sqr_sk(x: Int, q1: Int, q2: Int, q3: Int): Int = {
    if (x <= 1) x + q1
    else q2*x + sqr_sk(x - 2, q1, q2, q3) + q3
  }

  def main(args: Array[String]): Unit = {
    var continue = true

    val initialX = ((x: Int) => x >= 0).solve
    println("Initial x: " + initialX)

    // constraint is sqr(x, sqr_sk(x, q1, q2, q3))
    def cnstrGivenX(x0: Int): Constraint3[Int,Int,Int] = 
      ((q1: Int, q2: Int, q3: Int) => sqr(x0, sqr_sk(x0, q1, q2, q3)))

    def cnstrGivenParams(q1: Int, q2: Int, q3: Int): Constraint1[Int] =
      ((x: Int) => sqr(x, sqr_sk(x, q1, q2, q3)))

    var currentCnstr = cnstrGivenX(initialX)

    while (continue) {
      currentCnstr.find match {
        case Some((q1, q2, q3)) => {
          println("found candidate parameters q1 = " + q1 + ", q2 = " + q2 + ", q3 = " + q3)
          (((x: Int) => x >= 0) && (! cnstrGivenParams(q1, q2, q3))).find match {
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
