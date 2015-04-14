/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package utils

trait Interruptible {
  def interrupt(): Unit
  def recoverInterrupt(): Unit
}
