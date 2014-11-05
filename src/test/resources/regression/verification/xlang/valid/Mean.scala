import scala.collection.immutable.Set
import leon.annotation._
import leon.lang._

object Mean {

  def mean(x: Int, y: Int): Int = {
    require(x <= y && x >= 0 && y >= 0)
    x + (y - x)/2
  } ensuring(m => m >= x && m <= y)

}
