object IntOperations {
    def sum(a: Int, b: Int) : Int = {
        require(b >= 0)
        a + b
    } ensuring(_ >= a)


    // The body of the following function is not in PureScala
    // It will still get extracted, with "unknown body".
    // To disable the warnings, run with -P:funcheck:tolerant
    // (if it has a postcondition, you'll still get warnings
    // about the impossibility of verifying them)
    def factorial(v: Int) : Int = ({
      require(v >= 0)
      var c = 2
      var t = 1
      while(c <= v) {
        t = t * c
      }
      t
    }) ensuring(_ >= v)
}
