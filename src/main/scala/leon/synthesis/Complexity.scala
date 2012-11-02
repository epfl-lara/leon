package leon
package synthesis

import purescala.Trees._

abstract class Complexity[T <: Complexity[T]] extends Ordered[T] {
  def compare(that: T) = this.value - that.value

  def value : Int
}

case class TaskComplexity(t: Task) extends Complexity[TaskComplexity] {
  def value= { 
    Option(t.rule) match {
      case Some(r) =>
        100*t.problem.complexity.value + (100-r.priority) + t.minSolutionCost
      case None =>
        0
    }
  }
}

case class SolutionComplexity(s: Solution) extends Complexity[SolutionComplexity] {
  lazy val value = 42
}

case class ProblemComplexity(p: Problem) extends Complexity[ProblemComplexity] {
  lazy val value = 42
}
