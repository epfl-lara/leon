/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package synthesis
package rules

import evaluators.{DefaultEvaluator, EvaluationResults, Evaluator, PartialExpansionEvaluator}
import leon.grammars.enumerators.CandidateScorer.MeetsSpec
import leon.grammars.{Expansion, ExpansionExpr, Label}
import leon.grammars.enumerators._
import leon.purescala.Types.Untyped
import solvers._
import leon.purescala.Expressions._
import purescala.Constructors._
import purescala.ExprOps.simplestValue

object ProbDrivenEnumeration extends Rule("Prob. driven enumeration"){

  def instantiateOn(implicit hctx: SearchContext, p: Problem): Traversable[RuleInstantiation] = {
    val enum = hctx.findOptionOrDefault(SynthesisPhase.optEnum)

    List(new RuleInstantiation(s"Prob. driven enum. ($enum)") {
      def apply(hctx: SearchContext): RuleApplication = {

        import hctx.reporter._
        import hctx.program
        implicit val hctx0 = hctx

        val useOptTimeout = hctx.findOptionOrDefault(SynthesisPhase.optSTEOptTimeout)
        val maxGen     = 100000 // Maximum generated # of programs
        val solverTo   = 3000
        val fullEvaluator = new DefaultEvaluator(hctx, hctx.program)
        val partialEvaluator = new PartialExpansionEvaluator(hctx, hctx.program)
        val solverF    = SolverFactory.getFromSettings(hctx, program).withTimeout(solverTo)
        val outType    = tupleTypeWrap(p.xs map (_.getType))
        val topLabel   = Label(outType)//, List(Tagged(Tags.Top, 0, None)))
        val grammar    = grammars.default(hctx, p)
        val spec       = letTuple(p.xs, _: Expr, p.phi)
        var examples   = {
          val fromProblem = p.eb.examples.filter(_.isInstanceOf[InOutExample])
          if (fromProblem.nonEmpty) fromProblem
          else Seq(InExample(p.as.map(_.getType) map simplestValue))
        }
        val timers     = hctx.timers.enumeration

        val restartable = enum == "eqclasses"

        debug("Grammar:")
        grammar.printProductions(debug(_))

        // Evaluates a candidate against an example in the correct environment
        def evalCandidate(expr: Expr, evalr: Evaluator)(ex: Example): evalr.EvaluationResult = {
          timers.test.start()
          def withBindings(e: Expr) = p.pc.bindings.foldRight(e) {
            case ((id, v), bd) => let(id, v, bd)
          }

          val testExpr = ex match {
            case InExample(_) =>
              spec(expr)
            case InOutExample(_, outs) =>
              equality(expr, tupleWrap(outs))
          }

          val ans = evalr.eval(withBindings(testExpr), p.as.zip(ex.ins).toMap)
          timers.test.stop()
          ans
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
              examples = examples diff Seq(ex)
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

        val scorer = new CandidateScorer[Expr](partialTestCandidate,
                                               _ => examples,
                                               _.falseProduce(nt => ExpansionExpr(nt, Untyped)))
        def mkEnum = (enum match {
          case "eqclasses" => new EqClassesEnumerator(grammar, topLabel, problem.as, examples, program)
          case "bottomup"  => new ProbwiseBottomupEnumerator(grammar, topLabel)
          case "topdown"   => new ProbwiseTopdownEnumerator(grammar, topLabel, scorer)
          case _ =>
            warning("Enumerator not recognized, falling back to top-down...")
            new ProbwiseTopdownEnumerator(grammar, topLabel, scorer)
        }).iterator(topLabel).take(maxGen)
        var it = mkEnum

        /**
          * Second phase of STE: verify a given candidate by looking for CEX inputs.
          * Returns the potential solution and whether it is to be trusted.
          */
        def validateCandidate(expr: Expr): Option[Solution] = {
          timers.validate.start()
          debug(s"Validating $expr")
          val solver  = solverF.getNewSolver()
          EnumeratorStats.cegisIterCount += 1

          try {
            solver.assertCnstr(p.pc and not(spec(expr)))
            solver.check match {
              case Some(true) =>
                // Found counterexample! Exclude this program
                val model = solver.getModel
                val cex  = InExample(p.as.map(a => model.getOrElse(a, simplestValue(a.getType))))
                debug(s"Found cex $cex for $expr, restarting enum...")
                examples +:= cex
                if (restartable) {
                  it = mkEnum
                }
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
            timers.validate.stop()
            solverF.reclaim(solver)
          }
        }

        RuleClosed (
          if (!it.hasNext) Stream() else Stream.continually {
            val expr = it.next
            debug(s"Testing $expr")
            if (examples.exists(testCandidate(expr)(_).contains(false))) {
              None
            } else {
              validateCandidate(expr)
            }
          }.takeWhile(_ => it.hasNext).collect { case Some(e) => e }
        )
      }
    })
  }
}
