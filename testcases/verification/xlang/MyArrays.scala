import leon.lang.Map

object MyArrays {

  case class MyArray(var content: Map[BigInt, BigInt], size: BigInt) {
    require(size >= 0)

    def apply(i: BigInt): BigInt = {
      require(i >= 0 && i < size)
      content(i)
    }

    def set(i: BigInt, v: BigInt) = {
      require(i >= 0 && i < size)
      content = content + (i -> v)
    }

    /*
     * update seems to create a bug in Leon due to Scala magic syntax
     * and some rewriting to updated inside leon.
     */
     //def update(i: BigInt, v: BigInt) = { content = content + (i -> v) }

  }


  def update(a: MyArray): Unit = {
    require(a.size > 0)
    a.set(0, 10)
  } ensuring(_ => a(0) == 10)

}
