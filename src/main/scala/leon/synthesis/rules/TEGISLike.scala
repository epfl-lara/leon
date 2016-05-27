/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package synthesis
package rules

import purescala.Expressions._
import purescala.Types._
import purescala.Constructors._

import datagen._
import evaluators._
import codegen.CodeGenParams
import leon.grammars._
import leon.utils.GrowableIterable

import scala.collection.mutable.{HashMap => MutableMap}

import bonsai.enumerators._

abstract class TEGISLike(name: String) extends Rule(name) {
  case class TegisParams(
    grammar: ExpressionGrammar,
    rootLabel: TypeTree => Label,
    enumLimit: Int = 10000,
    reorderInterval: Int = 50
  )

  def getParams(sctx: SynthesisContext, p: Problem): TegisParams

  def instantiateOn(implicit hctx: SearchContext, p: Problem): Traversable[RuleInstantiation] = {

    List(new RuleInstantiation(this.name) {
      def apply(hctx: SearchContext): RuleApplication = {
        implicit val ci = hctx
        val params = getParams(hctx, p)
        val grammar = params.grammar

        val nTests = if (p.pc.isEmpty) 50 else 20

        val useVanuatoo = hctx.settings.cegisUseVanuatoo

        val baseExamples = if (p.isTestBased) {
          p.qebFiltered.examples.collect { case io: InOutExample => io }
        } else {
          p.qebFiltered.examples
        }

        val exampleGenerator: Iterator[Example] = if (p.isTestBased) {
          Iterator.empty
        } else if (useVanuatoo) {
          new VanuatooDataGen(hctx, hctx.program).generateFor(p.as, p.pc.toClause, nTests, 3000).map(InExample(_))
        } else {
          val evaluator = new DualEvaluator(hctx, hctx.program)
          new GrammarDataGen(evaluator, ValueGrammar).generateFor(p.as, p.pc.toClause, nTests, 1000).map(InExample(_))
        }

        val gi = new GrowableIterable[Example](baseExamples, exampleGenerator)

        val failedTestsStats = new MutableMap[Example, Int]().withDefaultValue(0)

        var n = 1
        def allExamples() = {
          if (n == 10 || n == 50 || n % 500 == 0) {
            gi.sortBufferBy(e => -failedTestsStats(e))
          }
          n += 1
          gi.iterator
        }

        if (gi.nonEmpty) {

          val evalParams = CodeGenParams.default.copy(maxFunctionInvocations = 2000)
          val evaluator  = new DualEvaluator(hctx, hctx.program, params = evalParams)

          val enum = new MemoizedEnumerator[Label, Expr, ProductionRule[Label, Expr]](grammar.getProductions)

          val targetType = tupleTypeWrap(p.xs.map(_.getType))

          val timers = hctx.timers.synthesis.rules.tegis

          val allExprs = enum.iterator(params.rootLabel(targetType))

          var candidate: Option[Expr] = None

          def findNext(): Option[Expr] = {
            candidate = None
            timers.generating.start()
            allExprs.take(params.enumLimit).takeWhile(e => candidate.isEmpty).foreach { e =>
              val exprToTest = letTuple(p.xs, e, p.phi)

              //sctx.reporter.debug("Got expression "+e.asString)
              timers.testing.start()
              if (allExamples().forall{
                case InExample(ins) =>
                  evaluator.eval(exprToTest, p.as.zip(ins).toMap).result == Some(BooleanLiteral(true))

                case InOutExample(ins, outs) =>
                  println("Evaluating "+e.asString+" with "+ins.map(_.asString))
                  evaluator.eval(e, p.as.zip(ins).toMap).result == Some(tupleWrap(outs))
              }) {
                candidate = Some(tupleWrap(Seq(e)))
              }
              timers.testing.stop()
            }
            timers.generating.stop()

            candidate
          }

          val toStream = Stream.continually(findNext()).takeWhile(_.nonEmpty).map( e =>
            Solution(BooleanLiteral(true), Set(), e.get, isTrusted = p.isTestBased)
          )

          RuleClosed(toStream)
        } else {
          hctx.reporter.debug("No test available")
          RuleFailed()
        }
      }
    })
  }
}
