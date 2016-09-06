import leon.lang._

object IntOperations {
    def sum(a: Int, b: Int) : Int = {
        require(b >= 0)
        val b2 = b - 1
        val b3 = b2 + 1
        a + b3
    } ensuring(_ >= a)


    // The body of the following function is not in PureScala
    // It will still get extracted, with "unknown body".
    // To disable the warnings, run with -P:leon:tolerant
    // (if it has a postcondition, you'll still get warnings
    // about the impossibility of verifying them)
    def factorial(v: Int) : Int = {
      require(v >= 0)
      var c = 2
      var t = 1
      while(c <= v) {
        t = t * c
      }
      t
    } ensuring(_ >= v)
}
