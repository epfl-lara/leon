/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package synthesis
package rules

import evaluators._
import leon.grammars.enumerators.CandidateScorer.MeetsSpec
import leon.grammars.{Expansion, ExpansionExpr, Label}
import leon.grammars.enumerators._
import purescala.Expressions._
import purescala.Constructors._
import purescala.ExprOps._
import purescala.DefOps._
import purescala.Common.Identifier
import utils.MutableExpr
import solvers._

object ProbDrivenEnumeration extends Rule("Prob. driven enumeration"){

  class NonDeterministicProgram(
    outerCtx: SearchContext,
    outerP: Problem,
    enum: String
  ) {

    import outerCtx.reporter._

    // Create a fresh solution function with the best solution around the
    // current STE as body
    val fd = {
      val fd = outerCtx.functionContext.duplicate()

      fd.fullBody = postMap {
        case src if src eq outerCtx.source =>
          val body = new PartialSolution(outerCtx.search.strat, true)(outerCtx)
            .solutionAround(outerCtx.currentNode)(MutableExpr(NoTree(outerP.outType)))
            .getOrElse(fatalError("Unable to get outer solution"))
            .term

          Some(body)
        case _ =>
          None
      }(fd.fullBody)

      fd
    }

    // Create a program replacing the synthesis source by the fresh solution
    // function
    val (outerToInner, innerToOuter, solutionBox, program) = {
      val t = funDefReplacer {
        case fd2 if fd2 == outerCtx.functionContext =>
          Some(fd)

        case fd2 =>
          Some(fd2.duplicate())
      }

      val innerProgram = transformProgram(t, outerCtx.program)

      val solutionBox = collect[MutableExpr] {
        case me: MutableExpr => Set(me)
        case _ => Set()
      }(fd.fullBody).head

      (t, t.inverse, solutionBox, innerProgram)
    }

    // It should be set to the solution you want to check at each time.
    // Usually it will either be cExpr or a concrete solution.
    private def setSolution(e: Expr) = solutionBox.underlying = e

    implicit val sctx = new SynthesisContext(outerCtx, outerCtx.settings, fd, program)

    val p = {
      implicit val bindings = Map[Identifier, Identifier]()

      Problem(
        as = outerP.as.map(outerToInner.transform),
        ws = outerToInner.transform(outerP.ws),
        pc = outerP.pc.map(outerToInner.transform),
        phi = outerToInner.transform(outerP.phi),
        xs = outerP.xs.map(outerToInner.transform),
        eb = outerP.eb.flatMap{ ex => List(ex.map(outerToInner.transform(_)(Map.empty))) }
      )
    }

    private val spec = letTuple(p.xs, solutionBox, p.phi)

    val useOptTimeout = sctx.findOptionOrDefault(SynthesisPhase.optSTEOptTimeout)
    val maxGen     = 100000 // Maximum generated # of programs
    val solverTo   = 3000
    val fullEvaluator = new TableEvaluator(sctx, program)
    val partialEvaluator = new PartialExpansionEvaluator(sctx, program)
    val solverF    = SolverFactory.getFromSettings(sctx, program).withTimeout(solverTo)
    val outType    = tupleTypeWrap(p.xs map (_.getType))
    val topLabel   = Label(outType)//, List(Tagged(Tags.Top, 0, None)))
    val grammar    = grammars.default(sctx, p)
    var examples   = {
      val fromProblem = p.eb.examples.filter(_.isInstanceOf[InOutExample])
      if (fromProblem.nonEmpty) fromProblem
      else Seq(InExample(p.as.map(_.getType) map simplestValue))
    }
    val timers     = sctx.timers.synthesis.applications.get("Prob-Enum")

    // Evaluates a candidate against an example in the correct environment
    def evalCandidate(expr: Expr, evalr: Evaluator)(ex: Example): evalr.EvaluationResult = timers.eval.timed {
      setSolution(expr)

      def withBindings(e: Expr) = p.pc.bindings.foldRight(e) {
        case ((id, v), bd) => let(id, v, bd)
      }

      val testExpr = ex match {
        case InExample(_) =>
          spec
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
          examples = examples diff Seq(ex)
          None
      }
    }

    def rawEvalCandidate(expr: Expr, ex: Example) = {
      setSolution(expr)

      def withBindings(e: Expr) = p.pc.bindings.foldRight(e) {
        case ((id, v), bd) => let(id, v, bd)
      }

      fullEvaluator.eval(withBindings(expr), p.as.zip(ex.ins).toMap)
    }

    def partialTestCandidate(expansion: Expansion[Label, Expr], ex: Example): MeetsSpec.MeetsSpec = {
      val expr = ExpansionExpr(expansion)
      val res = evalCandidate(expr, partialEvaluator)(ex)
      res match {
        case EvaluationResults.Successful(BooleanLiteral(true)) => MeetsSpec.YES
        case EvaluationResults.Successful(BooleanLiteral(false)) => MeetsSpec.NO
        case EvaluationResults.Successful(_) => MeetsSpec.NOTYET
        case EvaluationResults.RuntimeError(err) => MeetsSpec.NO
        case EvaluationResults.EvaluatorError(err) => MeetsSpec.NOTYET
      }
    }

    val restartable = enum == "eqclasses" || enum == "topdown-opt"

    def mkEnum = (enum match {
      case "eqclasses" => new EqClassesEnumerator(grammar, topLabel, p.as, examples, program)
      case "bottomup"  => new ProbwiseBottomupEnumerator(grammar, topLabel)
      case _ =>
        val disambiguate = enum match {
          case "topdown" => false
          case "topdown-opt" => true
          case _ =>
            warning(s"Enumerator $enum not recognized, falling back to top-down...")
            false
        }
        val scorer = new CandidateScorer[Label, Expr](partialTestCandidate, _ => examples, _.falseProduce(nt => ExpansionExpr(nt)))
        new ProbwiseTopdownEnumerator(grammar, topLabel, scorer, examples, rawEvalCandidate(_, _).result, disambiguate)
    }).iterator(topLabel).take(maxGen)
    var it = mkEnum
    debug("Grammar:")
    grammar.printProductions(debug(_))

    /**
      * Second phase of STE: verify a given candidate by looking for CEX inputs.
      * Returns the potential solution and whether it is to be trusted.
      */
    def validateCandidate(expr: Expr): Option[Solution] = {
      timers.validate.start()
      debug(s"Validating $expr")
      val solver = solverF.getNewSolver()
      EnumeratorStats.cegisIterCount += 1

      try {
        setSolution(expr)
        solver.assertCnstr(p.pc and not(spec))
        solver.check match {
          case Some(true) =>
            // Found counterexample! Exclude this program
            val model = solver.getModel
            val cex = InExample(p.as.map(a => model.getOrElse(a, simplestValue(a.getType))))
            debug(s"Found cex $cex for $expr")
            examples +:= cex
            timers.cegisIter.stop()
            timers.cegisIter.start()
            if (restartable) {
              debug("Restarting enum...")
              it = mkEnum
            }
            None

          case Some(false) =>
            debug("Proven correct!")
            timers.cegisIter.stop()
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

    def solutionStream = {
      timers.cegisIter.start()
      var sol: Option[Solution] = None
      while (sol.isEmpty && it.hasNext) {
        val expr = it.next
        debug(s"Testing $expr")
        sol = (if (examples.exists(testCandidate(expr)(_).contains(false))) {
          None
        } else {
          validateCandidate(expr)
        }).map( sol => sol.copy(term = innerToOuter.transform(sol.term)(Map())) )
      }

      sol.toStream

    }

  }

  def instantiateOn(implicit hctx: SearchContext, p: Problem): Traversable[RuleInstantiation] = {
    val enum = hctx.findOptionOrDefault(SynthesisPhase.optEnum)

    List(new RuleInstantiation(s"Prob. driven enum. ($enum)") {
      def apply(hctx: SearchContext): RuleApplication = {
        val ndProgram = new NonDeterministicProgram(hctx, p, enum)
        RuleClosed (ndProgram.solutionStream)
      }
    })
  }
}
