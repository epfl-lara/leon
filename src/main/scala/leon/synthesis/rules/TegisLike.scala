/* Copyright 2009-2014 EPFL, Lausanne */

package leon
package synthesis
package rules

import purescala.Trees._
import purescala.Common._
import purescala.Definitions._
import purescala.TypeTrees._
import purescala.Extractors._
import purescala.Constructors._

import evaluators._
import datagen._
import codegen.CodeGenParams

import utils._

import bonsai._
import bonsai.enumerators._

abstract class TEGISLike[T <% Typed](name: String) extends Rule(name) {
  def getGrammar(sctx: SynthesisContext, p: Problem): ExpressionGrammar[T]

  def getRootLabel(tpe: TypeTree): T

  val enumLimit = 10000;
  val testsReorderInterval = 50; // Every X test filterings, we reorder tests with most filtering first.

  def instantiateOn(sctx: SynthesisContext, p: Problem): Traversable[RuleInstantiation] = {

    List(new RuleInstantiation(p, this, SolutionBuilder.none, this.name, this.priority) {
      def apply(sctx: SynthesisContext): RuleApplication = {

        val grammar = getGrammar(sctx, p)

        var tests = p.getTests(sctx).map(_.ins).distinct
        if (tests.nonEmpty) {

          val evalParams            = CodeGenParams(maxFunctionInvocations = 2000, checkContracts = true)
          val evaluator             = new DualEvaluator(sctx.context, sctx.program, evalParams)

          val interruptManager      = sctx.context.interruptManager

          val enum = new MemoizedEnumerator[T, Expr](grammar.getProductions _)

          val (targetType, isWrapped) = if (p.xs.size == 1) {
            (p.xs.head.getType, false)
          } else {
            (TupleType(p.xs.map(_.getType)), true)
          }

          val timers = sctx.context.timers.synthesis.rules.tegis;

          val allExprs = enum.iterator(getRootLabel(targetType))

          var failStat = Map[Seq[Expr], Int]().withDefaultValue(0)

          var candidate: Option[Expr] = None
          var n = 1;

          def findNext(): Option[Expr] = {
            candidate = None
            timers.generating.start()
            allExprs.take(enumLimit).takeWhile(e => candidate.isEmpty).foreach { e =>
              val exprToTest = if (!isWrapped) {
                Let(p.xs.head, e, p.phi)
              } else {
                letTuple(p.xs, e, p.phi)
              }

              sctx.reporter.debug("Got expression "+e)
              timers.testing.start()
              if (tests.forall{ case t =>
                  val ts = System.currentTimeMillis
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
                if (isWrapped) {
                  candidate = Some(e)
                } else {
                  candidate = Some(Tuple(Seq(e)))
                }
              }
              timers.testing.stop()

              if (n % testsReorderInterval == 0) {
                tests = tests.sortBy(t => -failStat(t))
              }
              n += 1
            }
            timers.generating.stop()

            candidate
          }

          def toStream(): Stream[Solution] = {
            findNext() match {
              case Some(e) =>
                Stream.cons(Solution(BooleanLiteral(true), Set(), e, isTrusted = false), toStream())
              case None =>
                Stream.empty
            }
          }

          RuleClosed(toStream())
        } else {
          RuleFailed()
        }
      }
    })
  }
}
