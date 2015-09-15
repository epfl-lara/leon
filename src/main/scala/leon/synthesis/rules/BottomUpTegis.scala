/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package synthesis
package rules

import purescala.Expressions._
import purescala.Common._
import purescala.Types._
import purescala.Constructors._
import purescala.Quantification._
import evaluators._
import codegen.CodeGenParams

import utils._
import grammars._

import bonsai._
import bonsai.enumerators._

case object BottomUpTEGIS extends BottomUpTEGISLike[TypeTree]("BU TEGIS") {
  def getGrammar(sctx: SynthesisContext, p: Problem) = {
    Grammars.default(sctx, p)
  }

  def getRootLabel(tpe: TypeTree): TypeTree = tpe
}

abstract class BottomUpTEGISLike[T <% Typed](name: String) extends Rule(name) {
  def getGrammar(sctx: SynthesisContext, p: Problem): ExpressionGrammar[T]

  def getRootLabel(tpe: TypeTree): T

  def instantiateOn(implicit hctx: SearchContext, p: Problem): Traversable[RuleInstantiation] = {

    val tests = p.eb.valids.collect {
      case io: InOutExample => (io.ins, io.outs)
    }

    if (tests.nonEmpty) {
      List(new RuleInstantiation(this.name) {
        def apply(hctx: SearchContext): RuleApplication = {
          val sctx = hctx.sctx

          implicit val ctx = sctx.context

          val evalParams            = CodeGenParams.default.copy(maxFunctionInvocations = 2000)
          //val evaluator             = new CodeGenEvaluator(sctx.context, sctx.program, evalParams)
          //val evaluator             = new DefaultEvaluator(sctx.context, sctx.program)
          val evaluator             = new DualEvaluator(sctx.context, sctx.program, evalParams)

          val grammar               = getGrammar(sctx, p)

          val nTests = tests.size

          var compiled = Map[Generator[T, Expr], Vector[Vector[Expr]] => Option[Vector[Expr]]]()

          /**
           * Compile Generators to functions from Expr to Expr. The compiled
           * generators will be passed to the enumerator
           */
          def compile(gen: Generator[T, Expr]): Vector[Vector[Expr]] => Option[Vector[Expr]] = {
            compiled.getOrElse(gen, {
              val executor = if (gen.subTrees.isEmpty) {

                { (vecs: Vector[Vector[Expr]]) =>
                  val expr = gen.builder(Nil)
                  val res = tests.map { case (is, o) => (p.as zip is).toMap }.flatMap { case inputs =>
                    evaluator.eval(expr, inputs) match {
                      case EvaluationResults.Successful(out) => Some(out)
                      case _ => None
                    }
                  }.toVector

                  if (res.size == nTests) {
                    Some(res)
                  } else {
                    None
                  }
                }
              } else {
                val args = gen.subTrees.map(t => FreshIdentifier("arg", t.getType, true))
                val argsV = args.map(_.toVariable)
                val expr = gen.builder(argsV)
                val ev = evaluator.compile(expr, args).get

                { (vecs: Vector[Vector[Expr]]) =>
                  val res = (0 to nTests-1).toVector.flatMap { i =>
                    val inputs = new solvers.Model((args zip vecs.map(_(i))).toMap)
                    ev(inputs) match {
                      case EvaluationResults.Successful(out) => Some(out)
                      case _ =>
                        None
                    }
                  }

                  if (res.size == nTests) {
                    Some(res)
                  } else {
                    None
                  }
                }
              }

              compiled += gen -> executor
              executor
            })
          }

          val targetType   = tupleTypeWrap(p.xs.map(_.getType))
          val wrappedTests = tests.map { case (is, os) => (is, tupleWrap(os))}

          val enum = new BottomUpEnumerator[T, Expr, Expr](
            grammar.getProductions,
            wrappedTests,
            { (vecs, gen) =>
              compile(gen)(vecs)
            },
            3
          )


          val timers = sctx.context.timers.synthesis.rules.tegis

          val matches = enum.iterator(getRootLabel(targetType))

          if (matches.hasNext) {
            RuleClosed(Solution(BooleanLiteral(true), Set(), matches.next(), isTrusted = false))
          } else {
            RuleFailed()
          }
        }
      })
    } else {
      Nil
    }
  }
}
