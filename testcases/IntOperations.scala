object IntOperations {
    def sum(a: Int, b: Int) : Int = {
        require(b >= 0)
        a + b
    } ensuring(_ >= a)

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
