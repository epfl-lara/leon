/* Copyright 2009-2014 EPFL, Lausanne */

package leon
package synthesis
package heuristics

import purescala.Trees._
import purescala.TreeOps._
import purescala.Extractors._
import purescala.Constructors._

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
            phi = orJoin(es.map(not(_)))
            
          case Not(Or(es)) =>
            phi = andJoin(es.map(not(_)))

          case _ =>
        }

        phi match {
          case Or(os) =>
            List(rules.CaseSplit.split(os, p, "Inner case-split"))

          case And(as) =>
            val optapp = for ((a, i) <- as.zipWithIndex) yield {
              a match {
                case Or(os) =>
                  Some(rules.CaseSplit.split(os.map(o => andJoin(as.updated(i, o))), p, "Inner case-split"))

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

