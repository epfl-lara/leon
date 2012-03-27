package leon

object Utils {
  sealed class IsValid(val property : Boolean) {
    def holds : Boolean = {
      assert(property)
      property
    }
  }

  implicit def any2IsValid(x: Boolean) : IsValid = new IsValid(x)


  object InvariantFunction {
    def invariant(x: Boolean): Unit = ()
  }
  implicit def while2Invariant(u: Unit) = InvariantFunction
}
