/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package synthesis
package rules.unused

import purescala.Expressions._
import purescala.Common._
import purescala.Types._
import purescala.Constructors._
import evaluators._
import codegen.CodeGenParams

import grammars._

import bonsai.enumerators._

case object BottomUpTEGIS extends BottomUpTEGISLike("BU TEGIS") {
  def getGrammar(sctx: SynthesisContext, p: Problem) = {
    Grammars.default(sctx, p)
  }

  def getRootLabel(tpe: TypeTree): Label = Label(tpe)
}

abstract class BottomUpTEGISLike(name: String) extends Rule(name) {
  def getGrammar(sctx: SynthesisContext, p: Problem): ExpressionGrammar

  def getRootLabel(tpe: TypeTree): Label

  def instantiateOn(implicit hctx: SearchContext, p: Problem): Traversable[RuleInstantiation] = {

    val tests = p.eb.valids.collect {
      case io: InOutExample => (io.ins, io.outs)
    }

    if (tests.nonEmpty) {
      List(new RuleInstantiation(this.name) {
        def apply(hctx: SearchContext): RuleApplication = {

          val evalParams            = CodeGenParams.default.copy(maxFunctionInvocations = 2000)
          //val evaluator             = new CodeGenEvaluator(sctx.context, sctx.program, evalParams)
          //val evaluator             = new DefaultEvaluator(sctx.context, sctx.program)
          val evaluator             = new DualEvaluator(hctx, hctx.program, params = evalParams)

          val grammar               = getGrammar(hctx, p)

          val nTests = tests.size

          var compiled = Map[ProductionRule[Label, Expr], Vector[Vector[Expr]] => Option[Vector[Expr]]]()

          /**
           * Compile Generators to functions from Expr to Expr. The compiled
           * generators will be passed to the enumerator
           */
          def compile(gen: ProductionRule[Label, Expr]): Vector[Vector[Expr]] => Option[Vector[Expr]] = {
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

          val enum = new BottomUpEnumerator[Label, Expr, Expr, ProductionRule[Label, Expr]](
            grammar.getProductions(_)(hctx),
            wrappedTests,
            { (vecs, gen) =>
              compile(gen)(vecs)
            },
            3
          )

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
