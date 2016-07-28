import leon.lang._

object MutableGenerics2 {


  //should compile fine as not marked mutable
  case class Generic[B](x: B) {
    def dangerousPointer: B = x
  }

  case class M(var x: Int)

  def test(): Unit = {
    Generic[M](M(3)) //should fail as it is trying to instantiate a Mutable type
  }

}
