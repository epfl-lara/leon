import leon.lang._
import leon.lang.synthesis._

object Numerals {
  abstract class N
  case class S(succ: N) extends N
  case object Z extends N


  def plusone(a: N): N = {
    choose((x: N) => x match {
      case S(succ) => succ == a
      case Z => false
    })
  }
}
