/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package synthesis
package rules

import evaluators.{DefaultEvaluator, EvaluationResults, Evaluator, PartialExpansionEvaluator}
import leon.grammars.enumerators.CandidateScorer.MeetsSpec
import leon.grammars.{Expansion, ExpansionExpr, Label}
import leon.grammars.enumerators.{CandidateScorer, EnumeratorStats, ProbwiseBottomupEnumerator, ProbwiseTopdownEnumerator}
import leon.purescala.Types.Untyped
import solvers._
import purescala.Expressions.{BooleanLiteral, Expr}
import purescala.Constructors._
import purescala.ExprOps.simplestValue

object ProbDrivenEnumeration extends Rule("Prob. driven enumeration"){

  def instantiateOn(implicit hctx: SearchContext, p: Problem): Traversable[RuleInstantiation] = {
    val useTopDown = hctx.findOptionOrDefault(SynthesisPhase.optTopdownEnum)
    val tactic = if (useTopDown) "top-down" else "bottom-up"

    List(new RuleInstantiation(s"Prob. driven enum. ($tactic)") {
      def apply(hctx: SearchContext): RuleApplication = {

        import hctx.reporter._
        import hctx.program
        implicit val hctx0 = hctx

        // Maximum generated # of programs
        val maxGen = 10000000
        val solverTo = 3000
        val useOptTimeout = hctx.findOptionOrDefault(SynthesisPhase.optSTEOptTimeout)

        val fullEvaluator = new DefaultEvaluator(hctx, hctx.program)
        val partialEvaluator = new PartialExpansionEvaluator(hctx, hctx.program)
        val solverF    = SolverFactory.getFromSettings(hctx, program).withTimeout(solverTo)
        val outType    = tupleTypeWrap(p.xs map (_.getType))
        val grammar    = grammars.default(hctx, p)
        var examples   = p.eb.examples.toSet
        val spec       = letTuple(p.xs, _: Expr, p.phi)

        debug("Grammar:")
        grammar.printProductions(debug(_))

        // Evaluates a candidate against an example in the correct environment
        def evalCandidate(expr: Expr, evalr: Evaluator)(ex: Example) = {
          def withBindings(e: Expr) = p.pc.bindings.foldRight(e) {
            case ((id, v), bd) => let(id, v, bd)
          }

          val testExpr = ex match {
            case InExample(_) =>
              spec(expr)
            case InOutExample(_, outs) =>
              equality(expr, tupleWrap(outs))
          }

          evalr.eval(withBindings(testExpr), p.as.zip(ex.ins).toMap)
        }

        // Tests a candidate solution against an example in the correct environment
        def testCandidate(expr: Expr)(ex: Example): Option[Boolean] = {
          evalCandidate(expr, fullEvaluator)(ex) match {
            case EvaluationResults.Successful(value) =>
              Some(value == BooleanLiteral(true))
            case EvaluationResults.RuntimeError(err) =>
              debug(s"RE testing CE: $err. Example: $ex. Rejecting $expr")
              Some(false)
            case EvaluationResults.EvaluatorError(err) =>
              debug(s"Error testing CE: $err. Removing $ex")
              examples -= ex
              None
          }
        }

        def partialTestCandidate(expansion: Expansion[_, Expr], ex: Example): MeetsSpec.MeetsSpec = {
          val expr = ExpansionExpr(expansion, Untyped)
          val res = evalCandidate(expr, partialEvaluator)(ex)
          val ans = res match {
            case EvaluationResults.Successful(BooleanLiteral(true)) => MeetsSpec.YES
            case EvaluationResults.Successful(BooleanLiteral(false)) => MeetsSpec.NO
            case EvaluationResults.Successful(_) => MeetsSpec.NOTYET
            case EvaluationResults.RuntimeError(err) => MeetsSpec.NO
            case EvaluationResults.EvaluatorError(err) => MeetsSpec.NOTYET
          }

          ans
        }

        val scorer = new CandidateScorer[Expr](partialTestCandidate, _ => examples)

        /**
          * Second phase of STE: verify a given candidate by looking for CEX inputs.
          * Returns the potential solution and whether it is to be trusted.
          */
        def validateCandidate(expr: Expr): Option[Solution] = {
          debug(s"Validating $expr")
          val solver  = solverF.getNewSolver()
          EnumeratorStats.cegisIterCount += 1

          try {
            solver.assertCnstr(p.pc and not(spec(expr)))
            solver.check match {
              case Some(true) =>
                val model = solver.getModel
                val cex  = InExample(p.as.map(a => model.getOrElse(a, simplestValue(a.getType))))
                debug(s"Found cex $cex for $expr")
                // println(s"Found cex $cex for $expr")

                // Found counterexample! Exclude this program
                examples += cex
                None

              case Some(false) =>
                Some(Solution(BooleanLiteral(true), Set(), expr, isTrusted = true))

              case None =>
                if (useOptTimeout) {
                  info("STE could not prove the validity of the resulting expression")
                  // Interpret timeout in CE search as "the candidate is valid"
                  Some(Solution(BooleanLiteral(true), Set(), expr, isTrusted = false))

                } else {
                  // TODO: Make STE fail early when it times out when verifying 1 program?
                  None
                }
            }
          } finally {
            solverF.reclaim(solver)
          }
        }

        val enumerator = {
          if (useTopDown)
            new ProbwiseTopdownEnumerator(grammar, Label(outType), scorer)
          else
            new ProbwiseBottomupEnumerator(grammar, Label(outType))
        }

        val filtered =
          enumerator.iterator(Label(outType))
            .take(maxGen)
            .map(_._1)
            .map(passThrough(expr => debug(s"Testing $expr")))
            .filterNot { expr => examples.exists(testCandidate(expr)(_).contains(false)) }
            .map { validateCandidate }
            .flatten
            .toStream

        RuleClosed(filtered)
      }
    })
  }
}
