/* Copyright 2009-2013 EPFL, Lausanne */

package leon
package solvers
package smtlib

import utils._
import purescala._
import Common._
import Trees._
import Extractors._
import TreeOps._
import TypeTrees._
import Definitions._


abstract class SMTLIBSolver(val context: LeonContext,
                            val program: Program)
  extends IncrementalSolver with Interruptible with SMTLIBTarget {

  override def interrupt: Unit = {}
  override def recoverInterrupt(): Unit = {}

  override def name: String = "smt-"+targetName

  /**
   * Most of the solver functionality is defined, and thus extensible, in
   * SMTLIBTarget, which gets specialized based on how individual solvers
   * diverge from the SMTLib standard.
   */

  override def free() = {
    interpreter.free()
    out.close
  }

}
