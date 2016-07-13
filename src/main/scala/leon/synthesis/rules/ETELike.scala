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
import leon.grammars.aspects.Sized
import leon.utils.GrowableIterable

import scala.collection.mutable.{HashMap => MutableMap}

import bonsai.enumerators._

/** A common trait for all classes that implemen Example-guided Term Exploration
  *
  */
abstract class ETELike(name: String) extends Rule(name) {
  case class ETEParams(
    grammar: ExpressionGrammar,
    rootLabel: TypeTree => Label,
    minSize: Int,
    maxSize: Int
  )

  def getParams(sctx: SynthesisContext, p: Problem): ETEParams

  def instantiateOn(implicit hctx: SearchContext, p: Problem): Traversable[RuleInstantiation] = {

    List(new RuleInstantiation(this.name) {
      def apply(hctx: SearchContext): RuleApplication = {
        implicit val ci = hctx
        val params = getParams(hctx, p)
        val grammar = params.grammar

        val nTests = if (p.pc.isEmpty) 50 else 20

        val useVanuatoo = hctx.settings.steUseVanuatoo

        val baseExamples = if (p.isTestBased) {
          p.qebFiltered.examples.collect { case io: InOutExample => io }
        } else {
          p.qebFiltered.examples
        }

        ci.reporter.debug(ExamplesBank(baseExamples, Nil).asString("Tests"))

        val exampleGenerator: Iterator[Example] = if (p.isTestBased) {
          Iterator.empty
        } else if (useVanuatoo) {
          new VanuatooDataGen(hctx, hctx.program).generateFor(p.as, p.pc.toClause, nTests, 3000).map(InExample)
        } else {
          val evaluator = new DualEvaluator(hctx, hctx.program)
          new GrammarDataGen(evaluator, ValueGrammar).generateFor(p.as, p.pc.toClause, nTests, 1000).map(InExample)
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

          val timers = hctx.timers.synthesis.rules.ete

          val streams = for(size <- (params.minSize to params.maxSize).toIterator) yield {
            println("Size: "+size)
            val label = params.rootLabel(targetType).withAspect(Sized(size, true))

            val allExprs = enum.iterator(label)

            timers.generating.start()

            val candidates: Iterator[Expr] = allExprs.flatMap { e =>
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
                timers.testing.stop()
                Some(tupleWrap(Seq(e)))
              } else {
                timers.testing.stop()
                None
              }
            }
            timers.generating.stop()

            candidates
          }

          val solutions = streams.flatten.map { e =>
            Solution(BooleanLiteral(true), Set(), e, isTrusted = p.isTestBased)
          }

          RuleClosed(solutions.toStream)
        } else {
          hctx.reporter.debug("No test available")
          RuleFailed()
        }
      }
    })
  }
}
