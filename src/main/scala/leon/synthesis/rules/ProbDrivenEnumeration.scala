/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package synthesis
package rules

import evaluators.{EvaluationResults, DefaultEvaluator}
import leon.grammars._
import leon.grammars.aspects.Tagged
import leon.grammars.enumerators.{EqClassesEnumerator, ProbwiseTopdownEnumerator, ProbwiseBottomupEnumerator}
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
        val evaluator  = new DefaultEvaluator(hctx, hctx.program)
        val solverF    = SolverFactory.getFromSettings(hctx, program).withTimeout(solverTo)
        val outType    = tupleTypeWrap(p.xs map (_.getType))
        val topLabel   = Label(outType)//, List(Tagged(Tags.Top, 0, None)))
        val grammar    = grammars.default(hctx, p)
        val spec       = letTuple(p.xs, _: Expr, p.phi)
        var examples   = Seq(InExample(p.as.map(_.getType) map simplestValue))//p.eb.examples

        def mkEnum = (enum match {
          case "eqclasses" => new EqClassesEnumerator(grammar, topLabel, problem.as, examples, program)
          case "bottomup"  => new ProbwiseBottomupEnumerator(grammar, topLabel)
          case "topdown"   => new ProbwiseTopdownEnumerator(grammar, topLabel)
          case _ =>
            warning("Enumerator not recognized, falling back to top-down...")
            new ProbwiseTopdownEnumerator(grammar, topLabel)
        }).iterator(topLabel).take(maxGen)
        var it = mkEnum

        val restartable = enum == "eqclasses"

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
              examples = examples diff Seq(ex)
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
                // Found counterexample! Exclude this program
                val model = solver.getModel
                val cex  = InExample(p.as.map(a => model.getOrElse(a, simplestValue(a.getType))))
                debug(s"Found cex $cex for $expr, restarting enum...")
                examples +:= cex
                if (restartable) it = mkEnum
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
