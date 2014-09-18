/* Copyright 2009-2014 EPFL, Lausanne */

package leon
package synthesis
package rules

import solvers._
import solvers.z3._

import purescala.Trees._
import purescala.Common._
import purescala.Definitions._
import purescala.TypeTrees._
import purescala.TreeOps._
import purescala.TypeTreeOps._
import purescala.Extractors._
import purescala.ScalaPrinter
import purescala.Constructors._

import scala.collection.mutable.{Map=>MutableMap, ArrayBuffer}

import evaluators._
import datagen._
import codegen.CodeGenParams

import utils._

import bonsai._
import bonsai.enumerators._

case object BottomUpTEGIS extends BottomUpTEGISLike[TypeTree]("BU TEGIS") {
  def getGrammar(sctx: SynthesisContext, p: Problem) = {
    ExpressionGrammars.default(sctx, p)
  }

  def getRootLabel(tpe: TypeTree): TypeTree = tpe
}

abstract class BottomUpTEGISLike[T <% Typed](name: String) extends Rule(name) {
  def getGrammar(sctx: SynthesisContext, p: Problem): ExpressionGrammar[T]

  def getRootLabel(tpe: TypeTree): T

  def instantiateOn(sctx: SynthesisContext, p: Problem): Traversable[RuleInstantiation] = {
    var tests = p.getTests(sctx).collect {
      case io: InOutExample => (io.ins, io.outs)
    }

    if (tests.nonEmpty) {
      List(new RuleInstantiation(p, this, SolutionBuilder.none, this.name, this.priority) {
        def apply(sctx: SynthesisContext): RuleApplication = {

          val evalParams            = CodeGenParams(maxFunctionInvocations = 2000, checkContracts = true)
          //val evaluator             = new CodeGenEvaluator(sctx.context, sctx.program, evalParams)
          //val evaluator             = new DefaultEvaluator(sctx.context, sctx.program)
          val evaluator             = new DualEvaluator(sctx.context, sctx.program, evalParams)

          val interruptManager      = sctx.context.interruptManager

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
                val args = gen.subTrees.map(t => FreshIdentifier("arg", true).setType(t.getType))
                val argsV = args.map(_.toVariable)
                val expr = gen.builder(argsV)
                val ev = evaluator.compile(expr, args).get

                { (vecs: Vector[Vector[Expr]]) =>
                  val res = (0 to nTests-1).toVector.flatMap { i =>
                    val inputs = vecs.map(_(i))
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

          val (targetType, isWrapped, wrappedTests) = if (p.xs.size == 1) {
            (p.xs.head.getType, false, tests.map{ case (i, o) => (i, o.head) })
          } else {
            (TupleType(p.xs.map(_.getType)), true, tests.map{ case (i, o) => (i, Tuple(o)) })
          }

          val enum = new BottomUpEnumerator[T, Expr, Expr](
            grammar.getProductions,
            wrappedTests,
            { (vecs, gen) =>
              compile(gen)(vecs)
            },
            3
          )


          val timers = sctx.context.timers.synthesis.rules.tegis;

          val matches = enum.iterator(getRootLabel(targetType))

          if (matches.hasNext) {
            RuleClosed(Solution(BooleanLiteral(true), Set(), matches.next, isTrusted = false))
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
