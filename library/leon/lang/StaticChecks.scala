package leon.lang

import leon.annotation._
import scala.language.implicitConversions

object StaticChecks {

  case class Ensuring[A](x: A) {
    @library
    def ensuring(cond: (A) => Boolean): A = x
  }

  implicit def any2Ensuring[A](x: A): Ensuring[A] = Ensuring(x)

  def require(pred: Boolean): Unit = ()
  def assert(pred: Boolean): Unit = ()

}
