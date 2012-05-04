object InfiniteLoop {

  def infinite(): Int = {
    var i = 0
    var sum = 0
    while (i < 10) {
      sum = sum + i
    }
    sum
  }

}
