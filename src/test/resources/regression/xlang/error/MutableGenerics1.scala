import leon.lang._

object MutableGenerics1 {

  case class Generic[B : Mutable](x: B) {
    def dangerousPointer: B = x
  }

}
