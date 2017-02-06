import leon.lang._

object MutableGenerics3 {

  def id[A : Mutable](x: A): A = x

}
