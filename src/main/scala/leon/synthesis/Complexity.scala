package leon
package synthesis

import purescala.Trees._
import purescala.TreeOps._

abstract class Complexity[T <: Complexity[T]] extends Ordered[T] {
  def compare(that: T) = this.value - that.value

  def value : Int
}

abstract class AbsSolComplexity extends Complexity[AbsSolComplexity] {
  def value: Int
}

case class SolComplexity(s: Solution) extends AbsSolComplexity {
  lazy val value = {
    val chooses = collectChooses(s.toExpr)
    val chooseCost = chooses.foldLeft(0)((i, c) => i + (1000 * math.pow(2, c.vars.size).toInt + formulaSize(c.pred)))

    formulaSize(s.toExpr) + chooseCost
  }
}

case class FixedSolComplexity(c: Int) extends AbsSolComplexity {
  val value = c
}

case class ProblemComplexity(p: Problem) extends Complexity[ProblemComplexity] {
  lazy val value = {
    math.pow(2, p.xs.size).toInt + formulaSize(p.phi)
  }
}
