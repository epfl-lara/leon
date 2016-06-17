import leon.lang._
import leon.util.Random

object GlobalMutableField1 {

  case class A(var x: BigInt)

  val a: A = A(10)


  def update(): Unit = {
    a.x = a.x + 1
  }

}
