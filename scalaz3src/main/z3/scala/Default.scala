package z3.scala

import scala.annotation.implicitNotFound

/** A type class for Scala types that are representable in Z3 and that admit
 * a default value. The default value is used for model reconstruction when
 * no other value is available. */
@implicitNotFound(msg = "Cannot find a default value for ${A}.")
trait Default[A] {
  val value : A
}
