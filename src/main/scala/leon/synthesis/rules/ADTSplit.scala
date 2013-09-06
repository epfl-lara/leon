/* Copyright 2009-2013 EPFL, Lausanne */

package leon
package synthesis
package rules

import purescala.Trees._
import purescala.Common._
import purescala.TypeTrees._
import purescala.TreeOps._
import purescala.Extractors._
import purescala.Definitions._
import solvers._

case object ADTSplit extends Rule("ADT Split.") {
  def instantiateOn(sctx: SynthesisContext, p: Problem): Traversable[RuleInstantiation]= {
    val solver = SimpleSolverAPI(sctx.solverFactory.withTimeout(200L))

    val candidates = p.as.collect {
      case IsTyped(id, AbstractClassType(cd)) =>

        val optCases = for (dcd <- cd.knownDescendents.sortBy(_.id.name)) yield dcd match {
          case ccd : CaseClassDef =>
            val toSat = And(p.pc, CaseClassInstanceOf(ccd, Variable(id)))

            val isImplied = solver.solveSAT(toSat) match {
              case (Some(false), _) => true
              case _ => false
            }

            if (!isImplied) {
              Some(ccd)
            } else {
              None
            }
          case _ =>
            None
        }

        val cases = optCases.flatten

        if (!cases.isEmpty) {
          Some((id, cases))
        } else {
          None
        }
    }

    solver.free()

    candidates.collect{ _ match {
      case Some((id, cases)) =>
        val oas = p.as.filter(_ != id)

        val subInfo = for(ccd <- cases) yield {
           val args   = ccd.fieldsIds.map(id => FreshIdentifier(id.name, true).setType(id.getType)).toList

           val subPhi = subst(id -> CaseClass(ccd, args.map(Variable(_))), p.phi)
           val subPC  = subst(id -> CaseClass(ccd, args.map(Variable(_))), p.pc)
           val subProblem = Problem(args ::: oas, subPC, subPhi, p.xs)
           val subPattern = CaseClassPattern(None, ccd, args.map(id => WildcardPattern(Some(id))))

           (ccd, subProblem, subPattern)
        }


        val onSuccess: List[Solution] => Option[Solution] = {
          case sols =>
            var globalPre = List[Expr]()

            val cases = for ((sol, (ccd, problem, pattern)) <- (sols zip subInfo)) yield {
              globalPre ::= And(CaseClassInstanceOf(ccd, Variable(id)), sol.pre)

              SimpleCase(pattern, sol.term)
            }

            Some(Solution(Or(globalPre), sols.flatMap(_.defs).toSet, MatchExpr(Variable(id), cases)))
        }

        Some(RuleInstantiation.immediateDecomp(p, this, subInfo.map(_._2).toList, onSuccess, "ADT Split on '"+id+"'"))
      case _ =>
        None
    }}.flatten
  }
}
