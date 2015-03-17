/* Copyright 2009-2013 EPFL, Lausanne */

package leon
package solvers
package smtlib

import utils._
import purescala._
import Common._
import Expressions._
import Extractors._
import ExprOps._
import Types._
import Definitions._


abstract class SMTLIBSolver(val context: LeonContext,
                            val program: Program)
  extends IncrementalSolver with Interruptible with SMTLIBTarget {

  protected var interrupted = false

  override def interrupt(): Unit = {
    interrupted = true
    interpreter.interrupt()
  }
  override def recoverInterrupt(): Unit = {
    interrupted = false
  }

  override def name: String = "smt-"+targetName

  /**
   * Most of the solver functionality is defined, and thus extensible, in
   * SMTLIBTarget, which gets specialized based on how individual solvers
   * diverge from the SMTLib standard.
   */

  override def free() = {
    interpreter.free()
    reporter.ifDebug { _ => out.close() }
  }

}
