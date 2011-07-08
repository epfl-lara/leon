import cp.Definitions._
import cp.Terms._

object When {
  def main(args: Array[String]): Unit = {
    for (x <- ((x: Int) => x >= 0 && x < 4).lazyFindAll) {
      when (x < 3) {
        println("I'm assuming x is less than three")
      }

      println(when(x < 2) {
        "furthermore, less than two"
      } otherwise {
        "ok, it is not less than two"
      })

      val anInt: Int = when (x < 1) { 42 } // will throw an exception if x cannot be less than 1
    }
  }
}
