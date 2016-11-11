object ADTWithArray4 {

  /*
   * with --luckytest, this used to create negative array that crashes
   */

  case class A(x: Int)

  case class B(content: Array[A]) {
    require(content.length > 0)

    def contains(y: Int): Boolean = {
      content(0).x == y
    } ensuring(res => res)
  }

}
