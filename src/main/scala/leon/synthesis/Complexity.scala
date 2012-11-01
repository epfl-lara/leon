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
