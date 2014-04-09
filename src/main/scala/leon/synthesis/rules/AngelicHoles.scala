/* Copyright 2009-2014 EPFL, Lausanne */

package leon
package synthesis
package rules

import purescala.Common._
import purescala.Definitions._
import purescala.Trees._
import purescala.TreeOps._
import purescala.TypeTrees._
import purescala.Extractors._

// Synthesizing a function with Hole is actually synthesizing an Oracle, so Oracle becomes output:
// [[ a,o < Phi(a,o,x) > x ]]   --->  [[ a < Phi(a,o,x) > x, o ]]
case object AngelicHoles extends NormalizingRule("Angelic Holes") {
  def instantiateOn(sctx: SynthesisContext, p: Problem): Traversable[RuleInstantiation] = {
    val oracleClass = sctx.program.definedClasses.find(_.id.name == "Oracle").getOrElse {
      sctx.reporter.fatalError("Can't find Oracle class")
    }

    def isOracle(i: Identifier) = {
      i.getType match {
        case AbstractClassType(acd, _) if acd == oracleClass => true
        case _ => false
      }
    }

    if (usesHoles(p.phi)) {
      val (oracles, as) = p.as.partition(isOracle)

      if (oracles.nonEmpty) {
        val sub = p.copy(as = as, xs = p.xs ++ oracles)
        List(RuleInstantiation.immediateDecomp(p, this, List(sub), {
          case List(s) =>
            // We ignore the last output params that are oracles
            Some(s.project(0 until p.xs.size))

          case _ =>
            None
        }, "Hole Semantics"))
      } else {
        Nil
      }
    } else {
      Nil
    }
  }
}

