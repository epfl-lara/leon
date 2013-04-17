package lesynth
package evaluation

import scala.collection.mutable.ArrayBuffer

import leon._
import leon.evaluators._
import leon.evaluators.EvaluationResults._
import leon.purescala.Trees._
import leon.purescala.Definitions.{ FunDef, VarDecl, Program, ObjectDef }
import leon.purescala.Common.{ Identifier, FreshIdentifier }
import leon.purescala.TreeOps

import lesynth.examples._
import lesynth.ranking._

import insynth.util.logging.HasLogger

case class DefaultExampleRunner(program: Program, funDef: FunDef, ctx: LeonContext,
  candidates: Seq[Candidate], inputExamples: Seq[Example],
  maxSteps: Int = 2000) extends ExampleRunner(inputExamples) with HasLogger {

  private var _examples = ArrayBuffer(inputExamples.map(_.map): _*)
    
  override def addExamples(newExamples: Seq[Example]) = {
    super.addExamples(newExamples)
    _examples ++= newExamples.map(_.map)
  }

  val evaluationContext = ctx.copy(reporter = new SilentReporter)
  
  lazy val _evaluator = new DefaultEvaluator(evaluationContext, program)
  override def getEvaluator = _evaluator
  
  override def evaluate(expr: Expr, mapping: Map[Identifier, Expr]): Boolean = {
    finest("to evaluate: " + expr + " for mapping: " + mapping)
    getEvaluator.eval(expr, mapping) match {
      case Successful(BooleanLiteral(true)) =>
        finest("Eval succeded: EvaluationSuccessful(true)")
        true
      case m =>
        finest("Eval failed: " + m)
        false
    }
  }
  
  def evaluate(expr: Expr, args: Seq[Expr]): Boolean = {
    evaluate(expr, funDef.args.map(_.id).zip(args).toMap)
  }

  override def evaluateToResult(expr: Expr, mapping: Map[Identifier, Expr]) = {
    finest("to evaluate: " + expr + " for mapping: " + mapping)
    getEvaluator.eval(expr, mapping)
  }

  
  /** if the example runner knows about candidates and input examples, run by their indexes */
  def evaluate(candidateInd: Int, exampleInd: Int) =
    evaluate(candidates(candidateInd).prepareExpression, _examples(exampleInd))
  
  /** filter counterexamples according to an expression (precondition) */
  def filter(prec: Expr) = {
    entering("filter(" + prec + ")")
    finest("Old counterExamples.size: " + examples.size)
    _examples = _examples filter {
      evaluate(prec, _)
    }
    finest("New counterExamples.size: " + examples.size)
  }

  /** count how many examples pass */
  def countPassed(expressionToCheck: Expr) = {
    finest("count passed for expression to check: " + expressionToCheck)

    val (passed, failed) = examples.partition(
      ex => evaluate(expressionToCheck, ex.map)
    )
    
    (passed.size, passed)
  }

}