/* Copyright 2009-2013 EPFL, Lausanne */

package leon
package synthesis
package heuristics

import purescala.Trees._
import purescala.TreeOps._
import purescala.Extractors._

case object InnerCaseSplit extends Rule("Inner-Case-Split") with Heuristic {
  def instantiateOn(sctx: SynthesisContext, p: Problem): Traversable[RuleInstantiation] = {
    p.phi match {
      case Or(_) =>
        // Inapplicable in this case, normal case-split has precedence here.
        Nil
      case _ =>
        var phi = p.phi
        phi match {
          case Not(And(es)) =>
            phi = Or(es.map(Not(_)))
            
          case Not(Or(es)) =>
            phi = And(es.map(Not(_)))

          case _ =>
        }

        phi match {
          case Or(os) =>
            List(rules.CaseSplit.split(os, p, "Inner case-split"))

          case And(as) =>
            val optapp = for ((a, i) <- as.zipWithIndex) yield {
              a match {
                case Or(os) =>
                  Some(rules.CaseSplit.split(os.map(o => And(as.updated(i, o))), p, "Inner case-split"))

                case _ =>
                  None
              }
            }

            optapp.flatten

          case e =>
            Nil
        }
    }
  }

}

