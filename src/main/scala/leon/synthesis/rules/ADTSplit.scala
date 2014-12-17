/* Copyright 2009-2014 EPFL, Lausanne */

package leon
package synthesis
package rules

import purescala.Trees._
import purescala.Common._
import purescala.TypeTrees._
import purescala.TreeOps._
import purescala.Extractors._
import purescala.Constructors._
import purescala.Definitions._
import solvers._

case object ADTSplit extends Rule("ADT Split.") {
  def instantiateOn(sctx: SynthesisContext, p: Problem): Traversable[RuleInstantiation] = {
    val solver = SimpleSolverAPI(new TimeoutSolverFactory(sctx.solverFactory, 200L))

    val candidates = p.as.collect {
      case IsTyped(id, act @ AbstractClassType(cd, tpes)) =>

        val optCases = for (dcd <- cd.knownDescendents.sortBy(_.id.name)) yield dcd match {
          case ccd : CaseClassDef =>
            val cct = CaseClassType(ccd, tpes)
            val toSat = and(p.pc, CaseClassInstanceOf(cct, Variable(id)))

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
          Some((id, act, cases))
        } else {
          None
        }
    }

    candidates.collect{ _ match {
      case Some((id, act, cases)) =>
        val oas = p.as.filter(_ != id)

        val subInfo = for(ccd <- cases) yield {
           val cct    = CaseClassType(ccd, act.tps)

           val args   = cct.fields.map { vd => FreshIdentifier(vd.id.name, true).setType(vd.tpe) }.toList

           val subPhi = subst(id -> CaseClass(cct, args.map(Variable(_))), p.phi)
           val subPC  = subst(id -> CaseClass(cct, args.map(Variable(_))), p.pc)
           val subWS  = subst(id -> CaseClass(cct, args.map(Variable(_))), p.ws)
           val subProblem = Problem(args ::: oas, subWS, subPC, subPhi, p.xs)
           val subPattern = CaseClassPattern(None, cct, args.map(id => WildcardPattern(Some(id))))

           (cct, subProblem, subPattern)
        }


        val onSuccess: List[Solution] => Option[Solution] = {
          case sols =>
            var globalPre = List[Expr]()

            val cases = for ((sol, (cct, problem, pattern)) <- (sols zip subInfo)) yield {
              globalPre ::= and(CaseClassInstanceOf(cct, Variable(id)), sol.pre)

              SimpleCase(pattern, sol.term)
            }

            Some(Solution(orJoin(globalPre), sols.flatMap(_.defs).toSet, matchExpr(Variable(id), cases), sols.forall(_.isTrusted)))
        }

        Some(RuleInstantiation.immediateDecomp(p, this, subInfo.map(_._2).toList, onSuccess, "ADT Split on '"+id+"'"))
      case _ =>
        None
    }}.flatten
  }
}
