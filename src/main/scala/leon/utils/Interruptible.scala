package leon
package utils

trait Interruptible {
  def interrupt(): Unit
  def recoverInterrupt(): Unit
}
