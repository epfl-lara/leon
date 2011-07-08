import cp.Definitions._
import cp.Terms._

object Assuming {
  def main(args: Array[String]): Unit = {
    for (x <- ((x: Int) => x >= 0 && x < 4).lazyFindAll) {
      when (x < 3) {
        println("I'm assuming x is less than three")
      }

      println(when(x < 2) {
        "furthermore, less than two"
      } otherwise {
        "ok, not less than two"
      })

      val anInt: Int = when (x < 1) { 42 }

      // cif (x <= 1) {
      //   println(x)
      //   println("hi")
      // } celse {
      //   println(x)
      //   println("hola")
      // }

      // assuming(x == 0) {
      //   println(x)
      //   println("I assume this was zero!")
      // }
    }
  }
}
