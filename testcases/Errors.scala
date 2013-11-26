import leon.lang._

object Errors {
  def a(a: Int): Int = error[Int]("This is an error")
}

