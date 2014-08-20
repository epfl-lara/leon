import leon._
import leon.lang._

object Fields {
  case class Cl(x : Int) {
    lazy val lzy = x + 1

    val eager = x + 2

    def apply(y : Int) : Int = {
      eager + lzy + y
    } ensuring { _ == (2 * x + 3) + y }

  }

  def foo() : Int = {
    42
  }

  lazy val ox = 42

  val oy = ox + 12

  def lemma(cl : Cl) : Boolean = {
    cl.eager + cl.lzy > 2 * cl.x
  } holds 
}


