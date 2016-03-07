/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package datagen

import purescala.Expressions._
import purescala.Common._
import utils._

import java.util.concurrent.atomic.AtomicBoolean

trait DataGenerator extends Interruptible {
  implicit val debugSection = DebugSectionDataGen

  def generateFor(ins: Seq[Identifier], satisfying: Expr, maxValid: Int, maxEnumerated: Int): Iterator[Seq[Expr]]

  protected val interrupted: AtomicBoolean = new AtomicBoolean(false)

  def interrupt(): Unit = {
    interrupted.set(true)
  }

  def recoverInterrupt(): Unit = {
    interrupted.set(false)
  }
}
