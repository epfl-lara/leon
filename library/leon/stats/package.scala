/* Copyright 2009-2015 EPFL, Lausanne */

package leon

import java.lang.System
import leon.annotation._
import scala.{Long,Unit}

/**
 * A collection of methods that can be used to collect run-time statistics about Leon programs.
 * This is mostly used to test the resources properties of Leon programs
 */
package object stats {
  @ignore
  def timed[T](code: => T)(cont: Long => Unit): T = {
    var t1 = System.currentTimeMillis()
    val r = code
    cont((System.currentTimeMillis() - t1))
    r
  }

  @ignore
  def withTime[T](code: => T): (T, Long) = {
    var t1 = System.currentTimeMillis()
    val r = code
    (r, (System.currentTimeMillis() - t1))
  }
}
