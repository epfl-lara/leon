package leon.lang

import leon.annotation._
import scala.language.implicitConversions

object StaticChecks {

  @isabelle.typ(name = "Leon_Types.ensuring")
  @isabelle.constructor(name = "Leon_Types.ensuring.Ensuring")
  case class Ensuring[A](x: A) {
    @library
    def ensuring(cond: (A) => Boolean): A = x
  }

  implicit def any2Ensuring[A](x: A): Ensuring[A] = Ensuring(x)

  @library
  def require(pred: Boolean): Unit = ()

  @library
  def assert(pred: Boolean): Unit = ()

}
