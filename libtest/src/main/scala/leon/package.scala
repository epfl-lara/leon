import leon.annotation._
import scala.annotation.elidable
import scala.annotation.elidable._

/**
 * A collection of methods that can be used to collect run-time statistics about Leon programs.
 * This is mostly used to test the resources properties of Leon programs
 */
package object leon {

  /**
   * Stubs of ensuring and require that do not check contracts.
   * Enable this if you want running time statistics without executing contracts.
   */
  @ignore  
  implicit class Ensuring[A](private val self: A) extends AnyVal {
    @inline
    def ensuring(cond: A => Boolean): A = { self }
  }
  
  @ignore  
  def require(arg: => Boolean) {}
}
