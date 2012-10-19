package leon

object Utils {
  sealed class IsValid(val property : Boolean) {
    def holds : Boolean = {
      assert(property)
      property
    }
  }

  implicit def any2IsValid(x: Boolean) : IsValid = new IsValid(x)

  def epsilon[A](pred: (A) => Boolean): A = throw new RuntimeException("Implementation not supported")

  object InvariantFunction {
    def invariant(x: Boolean): Unit = ()
  }
  implicit def while2Invariant(u: Unit) = InvariantFunction


  def waypoint[A](i: Int, expr: A): A = expr

  private def noChoose = throw new RuntimeException("Implementation not supported")

  def choose[A](predicate: A => Boolean) = noChoose
  def choose[A, B](predicate: (A, B) => Boolean) = noChoose
  def choose[A, B, C](predicate: (A, B, C) => Boolean) = noChoose
  def choose[A, B, C, D](predicate: (A, B, C, D) => Boolean) = noChoose
  def choose[A, B, C, D, E](predicate: (A, B, C, D, E) => Boolean) = noChoose
  def choose[A, B, C, D, E, F](predicate: (A, B, C, D, E, F) => Boolean) = noChoose
  def choose[A, B, C, D, E, F, G](predicate: (A, B, C, D, E, F, G) => Boolean) = noChoose
}
