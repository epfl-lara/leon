/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package synthesis
package rules

import purescala.Expressions._
import purescala.Types._
import purescala.Constructors._

import datagen._
import evaluators._
import codegen.CodeGenParams
import grammars._

import scala.collection.mutable.{HashMap => MutableMap}

import bonsai.enumerators._

abstract class TEGISLike[T <: Typed](name: String) extends Rule(name) {
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

        implicit val ctx = sctx.context

        val params = getParams(sctx, p)
        val grammar = params.grammar

        val nTests = if (p.pc == BooleanLiteral(true)) 50 else 20

        val useVanuatoo      = sctx.settings.cegisUseVanuatoo.getOrElse(false)

        val inputGenerator: Iterator[Seq[Expr]] = if (useVanuatoo) {
          new VanuatooDataGen(sctx.context, sctx.program).generateFor(p.as, p.pc, nTests, 3000)
        } else {
          val evaluator = new DualEvaluator(sctx.context, sctx.program, CodeGenParams.default)
          new GrammarDataGen(evaluator, ValueGrammar).generateFor(p.as, p.pc, nTests, 1000)
        }

        val gi = new GrowableIterable[Seq[Expr]](p.eb.examples.map(_.ins).distinct, inputGenerator)

        val failedTestsStats = new MutableMap[Seq[Expr], Int]().withDefaultValue(0)

        def hasInputExamples = gi.nonEmpty

        var n = 1
        def allInputExamples() = {
          if (n == 10 || n == 50 || n % 500 == 0) {
            gi.sortBufferBy(e => -failedTestsStats(e))
          }
          n += 1
          gi.iterator
        }

        var tests = p.eb.valids.map(_.ins).distinct

        if (gi.nonEmpty) {

          val evalParams            = CodeGenParams.default.copy(maxFunctionInvocations = 2000)
          val evaluator             = new DualEvaluator(sctx.context, sctx.program, evalParams)

          val enum = new MemoizedEnumerator[T, Expr, Generator[T, Expr]](grammar.getProductions)

          val targetType = tupleTypeWrap(p.xs.map(_.getType))

          val timers = sctx.context.timers.synthesis.rules.tegis

          val allExprs = enum.iterator(params.rootLabel(targetType))

          var candidate: Option[Expr] = None
          var n = 1

          def findNext(): Option[Expr] = {
            candidate = None
            timers.generating.start()
            allExprs.take(params.enumLimit).takeWhile(e => candidate.isEmpty).foreach { e =>
              val exprToTest = letTuple(p.xs, e, p.phi)

              //sctx.reporter.debug("Got expression "+e.asString)
              timers.testing.start()
              if (allInputExamples().forall{ t =>
                val res = evaluator.eval(exprToTest, p.as.zip(t).toMap) match {
                  case EvaluationResults.Successful(BooleanLiteral(true)) =>
                    //sctx.reporter.debug("Test "+t.map(_.asString)+" passed!")
                    true
                  case _ =>
                    //sctx.reporter.debug("Test "+t.map(_.asString)+" failed!")
                    failedTestsStats += t -> (failedTestsStats(t)+1)
                    false
                }
                res
              }) {
                candidate = Some(tupleWrap(Seq(e)))
              }
              timers.testing.stop()
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
