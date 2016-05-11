/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package synthesis
package rules

import purescala.Common._
import purescala.DefOps._
import purescala.Expressions._
import purescala.TypeOps.unify
import purescala.Constructors._
import purescala.ExprOps._
import purescala.Definitions._
import purescala.Extractors._
import leon.solvers.{SolverFactory, SimpleSolverAPI}
import leon.utils.Simplifiers

object Abduction extends Rule("Abduction") {
  override def instantiateOn(implicit hctx: SearchContext, p: Problem): Traversable[RuleInstantiation] = {
    Nil
  }

}
