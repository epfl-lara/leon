import leon.annotation._
import leon.lang._

object SimpleAdditionBase {


  def chooser(x: Int): Char = x match {
    case 1 => 'a'
    case 2 => 'b'
  }
}
