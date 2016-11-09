/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package synthesis
package rules

import evaluators.{EvaluationResults, DefaultEvaluator}
import leon.grammars.Label
import leon.grammars.enumerators.{ProbwiseTopdownEnumerator, ProbwiseBottomupEnumerator}
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
        val maxGen = 100000
        val solverTo = 3000
        val useOptTimeout = hctx.findOptionOrDefault(SynthesisPhase.optSTEOptTimeout)

        val evaluator  = new DefaultEvaluator(hctx, hctx.program)
        val solverF    = SolverFactory.getFromSettings(hctx, program).withTimeout(solverTo)
        val outType    = tupleTypeWrap(p.xs map (_.getType))
        val grammar    = grammars.default(hctx, p)
        var examples   = p.eb.examples.toSet
        val spec       = letTuple(p.xs, _: Expr, p.phi)
        val enumerator = {
          if (useTopDown)
            new ProbwiseTopdownEnumerator(grammar, Label(outType))
          else
            new ProbwiseBottomupEnumerator(grammar, Label(outType))
        }

        debug("Grammar:")
        grammar.printProductions(debug(_))

        // Tests a candidate solution against an example in the correct environment
        def testCandidate(expr: Expr)(ex: Example): Option[Boolean] = {
          def withBindings(e: Expr) = p.pc.bindings.foldRight(e) {
            case ((id, v), bd) => let(id, v, bd)
          }
          val testExpr = ex match {
            case InExample(_) =>
              spec(expr)

            case InOutExample(_, outs) =>
              equality(expr, tupleWrap(outs))
          }

          val res = evaluator.eval(withBindings(testExpr), p.as.zip(ex.ins).toMap)

          res match {
            case EvaluationResults.Successful(ex) =>
              Some(ex == BooleanLiteral(true))

            case EvaluationResults.RuntimeError(err) =>
              debug(s"RE testing CE: $err. Example: $ex. Rejecting $expr")
              Some(false)

            case EvaluationResults.EvaluatorError(err) =>
              debug(s"Error testing CE: $err. Removing $ex")
              examples -= ex
              None
          }

        }


        /**
          * Second phase of STE: verify a given candidate by looking for CEX inputs.
          * Returns the potential solution and whether it is to be trusted.
          */
        def validateCandidate(expr: Expr): Option[Solution] = {
          debug(s"Validating $expr")
          val solver  = solverF.getNewSolver()

          try {
            solver.assertCnstr(p.pc and not(spec(expr)))
            solver.check match {
              case Some(true) =>
                val model = solver.getModel
                val cex  = InExample(p.as.map(a => model.getOrElse(a, simplestValue(a.getType))))
                debug(s"Found cex $cex for $expr")

                // Found counterexample! Exclude this program
                examples += cex
                None

              case Some(false) =>
                Some(Solution(BooleanLiteral(true), Set(), expr, true))

              case None =>
                if (useOptTimeout) {
                  info("STE could not prove the validity of the resulting expression")
                  // Interpret timeout in CE search as "the candidate is valid"
                  Some(Solution(BooleanLiteral(true), Set(), expr, false))

                } else {
                  // TODO: Make STE fail early when it times out when verifying 1 program?
                  None
                }
            }
          } finally {
            solverF.reclaim(solver)
          }
        }

        val filtered =
          enumerator.iterator(Label(outType))
            .take(maxGen)
            .map(_._1)
            .map(passThrough(expr => debug(s"Testing $expr")))
            .filter { expr => examples.forall(testCandidate(expr)(_).contains(true)) }
            .map { validateCandidate }
            .flatten
            .toStream

        RuleClosed(filtered)
      }
    })
  }
}
