/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package solvers
package smtlib

import purescala.Common.Identifier
import purescala.Expressions.Expr
import verification.VC

trait SMTLIBQuantifiedSolver {
  this: SMTLIBSolver with SMTLIBQuantifiedTarget =>

  // We need to know the function context.
  // The reason is we do not want to assume postconditions of functions referring to
  // the current function, as this may make the proof unsound
  override def assertVC(vc: VC) = {
    currentFunDef = Some(vc.fd)
    assertCnstr(withInductiveHyp(vc.condition))
  }

  // Normally, UnrollingSolver tracks the input variable, but this one
  // is invoked alone so we have to filter them here
  override def getModel: Model = {
    val filter = currentFunDef.map{ _.params.map{_.id}.toSet }.getOrElse( (_:Identifier) => true )
    getModel(filter)
  }

}
