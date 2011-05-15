import cp.Definitions._

object Coordinates {
  def main(args : Array[String]) : Unit = {
    println("Size X ?")
    val x = Console.readInt
    println("Size Y ?")
    val y = Console.readInt
    println("Size Z ?")
    val z = Console.readInt

    println("Index ?")
    val i = Console.readInt

    val (j, k, l) = ((j: Int, k: Int, l: Int) => ( 
         i == l * (x * y) + k * x + j )
      && 0 <= j && j < x
      && 0 <= k && k < y
      && 0 <= l && l < z
    ).solve

    println("Index " + i + " corresponds to coordinate (" + j + ", " + k + ", " + l + ") in the space.")
  }
}
