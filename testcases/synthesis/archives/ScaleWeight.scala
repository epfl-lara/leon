import leon.lang._
import leon.lang.synthesis._

object ScaleWeight {

  def sw(weight: Int): (Int, Int, Int, Int) = choose((w4:Int,w3:Int,w2:Int,w1:Int) => (
    w1 + 3 * w2 + 9 * w3 + 27 * w4 == weight
    && -1 <= w1 && w1 <= 1
    && -1 <= w2 && w2 <= 1
    && -1 <= w3 && w3 <= 1
    && -1 <= w4 && w4 <= 1
  ))
}
