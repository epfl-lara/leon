import scala.collection.immutable.Set
import funcheck.Annotations._
import funcheck.Utils._

object IntSynth {
  def spec(time : Int, m : Int, s : Int) : Boolean = {
    require(0 <= time)
    time == 60 * m + s &&
    0 <= m && 0 <= s && s < 60
  }
  def f200(m : Int, s : Int) : Boolean = {
    !spec(200, m, s)
  } holds
}
