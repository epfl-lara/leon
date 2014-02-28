/* Copyright 2009-2013 EPFL, Lausanne */

package leon
package datagen

import purescala.Trees._
import purescala.Common._
import utils._

import java.util.concurrent.atomic.AtomicBoolean

trait DataGenerator extends Interruptible {
  def generateFor(ins: Seq[Identifier], satisfying: Expr, maxValid: Int, maxEnumerated: Int): Iterator[Seq[Expr]];

  protected val interrupted: AtomicBoolean = new AtomicBoolean(false)

  def interrupt(): Unit = {
    interrupted.set(true)
  }

  def recoverInterrupt(): Unit = {
    interrupted.set(false)
  }
}
