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
    val solver = SimpleSolverAPI(new TimeoutSolverFactory(sctx.solverFactory, 200L))

    val candidates = p.as.collect {
      case IsTyped(id, act @ AbstractClassType(cd, _)) =>

        val optCases = for (dct <- act.knownDescendents.sortBy(_.classDef.id.name)) yield dct match {
          case cct @ CaseClassType(_, _) =>
            val toSat = And(p.pc, CaseClassInstanceOf(cct, Variable(id)))

            val isImplied = solver.solveSAT(toSat) match {
              case (Some(false), _) => true
              case _ => false
            }

            if (!isImplied) {
              Some(cct)
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

    candidates.collect{ _ match {
      case Some((id, cases)) =>
        val oas = p.as.filter(_ != id)

        val subInfo = for(cct <- cases) yield {
           val args   = cct.fieldsIds.map(id => FreshIdentifier(id.name, true).setType(id.getType)).toList

           val subPhi = subst(id -> CaseClass(cct, args.map(Variable(_))), p.phi)
           val subPC  = subst(id -> CaseClass(cct, args.map(Variable(_))), p.pc)
           val subProblem = Problem(args ::: oas, subPC, subPhi, p.xs)
           val subPattern = CaseClassPattern(None, cct, args.map(id => WildcardPattern(Some(id))))

           (cct, subProblem, subPattern)
        }


        val onSuccess: List[Solution] => Option[Solution] = {
          case sols =>
            var globalPre = List[Expr]()

            val cases = for ((sol, (cct, problem, pattern)) <- (sols zip subInfo)) yield {
              globalPre ::= And(CaseClassInstanceOf(cct, Variable(id)), sol.pre)

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
