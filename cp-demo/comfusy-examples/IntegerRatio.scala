import cp.Definitions._

object IntegerRatio {
    def main(args : Array[String]) : Unit = {
        println("a ? ")
        val a = Console.readInt
        println("b ? ")
        val b = Console.readInt
        try {
          val x = ((x: Int) => a * x == b || b * x == a).solve
          println("Ratio is " + x)
        } catch {
          case e: UnsatisfiableConstraintException => println("Couldn't find an integer ratio between 'a' and 'b'.")
        }
    }
}
