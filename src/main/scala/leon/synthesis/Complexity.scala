package leon
package synthesis

abstract class Complexity extends Ordered[Complexity] {
  def compare(that: Complexity): Int = (this.compute, that.compute) match {
    case (x, y) if x < y => -1
    case (x, y) if x > y => +1
    case _ => 0
  }

  def compute : Double
}

case class TaskComplexity(p: Problem, r: Option[Rule]) extends Complexity {
  def compute = { 
    r match {
      case Some(r) =>
        100*p.complexity.compute + (100-r.priority)
      case None =>
        0
    }
  }
}

object Complexity {
  val zero = new Complexity {
    override def compute = 0
    override def toString = "0"
  }
  val max = new Complexity {
    override def compute = 42
    override def toString = "MAX"
  }
}
