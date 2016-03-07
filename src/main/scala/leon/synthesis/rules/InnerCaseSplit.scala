/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package synthesis
package rules

import purescala.Expressions._
import purescala.Constructors._

case object InnerCaseSplit extends Rule("Inner-Case-Split"){
  def instantiateOn(implicit hctx: SearchContext, p: Problem): Traversable[RuleInstantiation] = {
    p.phi match {
      case Or(_) =>
        // Inapplicable in this case, normal case-split has precedence here.
        Nil
      case _ =>
        var phi = p.phi
        phi match {
          case Not(And(es)) =>
            phi = orJoin(es.map(not))
            
          case Not(Or(es)) =>
            phi = andJoin(es.map(not))

          case _ =>
        }

        phi match {
          case Or(os) =>
            List(rules.CaseSplit.split(os, "Inner case-split"))

          case And(as) =>
            val optapp = for ((a, i) <- as.zipWithIndex) yield {
              a match {
                case Or(os) =>
                  Some(rules.CaseSplit.split(os.map(o => andJoin(as.updated(i, o))), "Inner case-split"))

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

