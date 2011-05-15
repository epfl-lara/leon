import cp.Definitions._

object Divides5And7 {
  def main(args : Array[String]) : Unit = {
    println("Give me a number.")
    val y = Console.readInt

    val (b, c, _, _) = ((b:Int,c:Int,a1:Int,a2:Int) => {
        y + b == 5 * a1 && y + c == 7 * a2 && a1 != 0 && a2 != 0 && b > 0 && c > 0
    }).solve

    println(y + " + " + b + " = " + (y+b) + " ...and that's a multiple of 5.")
    println(y + " + " + c + " = " + (y+c) + " ...and that's a multiple of 7.")
  }
}
