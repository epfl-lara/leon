package leon
package synthesis

import purescala.Trees._
import purescala.TreeOps._

abstract class Complexity[T <: Complexity[T]] extends Ordered[T] {
  def compare(that: T) = this.value - that.value

  def value : Int
}

abstract class SolutionComplexity extends Complexity[SolutionComplexity] {
  def value: Int
}

case class ConcreteSolutionComplexity(s: Solution) extends SolutionComplexity {
  lazy val value = {
    val chooses = collectChooses(s.term)
    val chooseCost = chooses.foldLeft(0)((i, c) => i + (1000 * math.pow(2, c.vars.size).toInt + formulaSize(c.pred)))

    formulaSize(s.pre) + formulaSize(s.term) + chooseCost
  }
}

case class FixedSolutionComplexity(c: Int) extends SolutionComplexity {
  val value = c
}

case class ProblemComplexity(p: Problem) extends Complexity[ProblemComplexity] {
  lazy val value = {
    math.pow(2, p.xs.size).toInt + formulaSize(p.phi)
  }
}
