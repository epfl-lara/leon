import cp.Definitions._

object ScaleWeights {
  def main(args: Array[String]): Unit = {
    println("Give me a weight: ")
    val weight: Int = Console.readInt

    try {
      val (w1,w2,w3,w4) = ((w1:Int,w2:Int,w3:Int,w4:Int) => (
           w1 + 3 * w2 + 9 * w3 + 27 * w4 == weight
        && -1 <= w1 && w1 <= 1
        && -1 <= w2 && w2 <= 1
        && -1 <= w3 && w3 <= 1
        && -1 <= w4 && w4 <= 1
      )).solve
      println("Put what you think weights " + weight + " to the left, then")
      println("Put 1         : " + numToPlace(w1))
      println("Put 3         : " + numToPlace(w2))
      println("Put 9         : " + numToPlace(w3))
      println("Put 27        : " + numToPlace(w4))
    } catch {
      case e: UnsatisfiableConstraintException => println("Sorry, cannot measure " + weight + " with weights 1,3,9 and 27.")
    }
  }

  def numToPlace(i: Int): String = i match {
    case -1 => "to the left"
    case  0 => "nowhere"
    case  1 => "to the right"
    case  _ => "??? " + i
  }
}
