/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package synthesis
package rules

import purescala.Expressions._
import purescala.Types._
import purescala.Constructors._

import evaluators._
import codegen.CodeGenParams

import utils._

import bonsai.enumerators._

abstract class TEGISLike[T <% Typed](name: String) extends Rule(name) {
  case class TegisParams(
    grammar: ExpressionGrammar[T],
    rootLabel: TypeTree => T,
    enumLimit: Int = 10000,
    reorderInterval: Int = 50
  )

  def getParams(sctx: SynthesisContext, p: Problem): TegisParams

  def instantiateOn(implicit hctx: SearchContext, p: Problem): Traversable[RuleInstantiation] = {

    List(new RuleInstantiation(this.name) {
      def apply(hctx: SearchContext): RuleApplication = {
        val sctx = hctx.sctx

        val params = getParams(sctx, p)
        val grammar = params.grammar

        val ef = new ExamplesFinder(sctx.context, sctx.program)
        var tests = ef.extractTests(p).map(_.ins).distinct
        if (tests.nonEmpty) {

          val evalParams            = CodeGenParams.default.copy(maxFunctionInvocations = 2000)
          val evaluator             = new DualEvaluator(sctx.context, sctx.program, evalParams)

          val enum = new MemoizedEnumerator[T, Expr](grammar.getProductions)

          val targetType = tupleTypeWrap(p.xs.map(_.getType))

          val timers = sctx.context.timers.synthesis.rules.tegis

          val allExprs = enum.iterator(params.rootLabel(targetType))

          var failStat = Map[Seq[Expr], Int]().withDefaultValue(0)

          var candidate: Option[Expr] = None
          var n = 1

          def findNext(): Option[Expr] = {
            candidate = None
            timers.generating.start()
            allExprs.take(params.enumLimit).takeWhile(e => candidate.isEmpty).foreach { e =>
              val exprToTest = letTuple(p.xs, e, p.phi)

              sctx.reporter.debug("Got expression "+e)
              timers.testing.start()
              if (tests.forall{ t =>
                val res = evaluator.eval(exprToTest, p.as.zip(t).toMap) match {
                  case EvaluationResults.Successful(BooleanLiteral(true)) =>
                    sctx.reporter.debug("Test "+t+" passed!")
                    true
                  case _ =>
                    sctx.reporter.debug("Test "+t+" failed on "+e)
                    failStat += t -> (failStat(t) + 1)
                    false
                }
                res
              }) {
                candidate = Some(tupleWrap(Seq(e)))
              }
              timers.testing.stop()

              if (n % params.reorderInterval == 0) {
                tests = tests.sortBy(t => -failStat(t))
              }
              n += 1
            }
            timers.generating.stop()

            candidate
          }

          def toStream: Stream[Solution] = {
            findNext() match {
              case Some(e) =>
                Stream.cons(Solution(BooleanLiteral(true), Set(), e, isTrusted = false), toStream)
              case None =>
                Stream.empty
            }
          }

          RuleClosed(toStream)
        } else {
          sctx.reporter.debug("No test available")
          RuleFailed()
        }
      }
    })
  }
}
