package leon.synthesis.condabd
package evaluation

import scala.collection.mutable.ArrayBuffer

import leon._
import leon.evaluators._
import leon.evaluators.EvaluationResults._
import leon.purescala.Trees._
import leon.purescala.Definitions.{ TypedFunDef, FunDef, ValDef, Program, ModuleDef }
import leon.purescala.Common.{ Identifier, FreshIdentifier }
import leon.purescala.TreeOps
import leon.codegen.CodeGenParams

import examples._
import ranking._

import _root_.insynth.util.logging.HasLogger

case class CodeGenExampleRunner(program: Program, tfd: TypedFunDef, ctx: LeonContext,
  candidates: Seq[Candidate], inputExamples: Seq[Example],
  params: CodeGenParams = CodeGenParams(maxFunctionInvocations = 200, checkContracts = true)) extends ExampleRunner(inputExamples) with HasLogger {

  private var _examples = ArrayBuffer(transformExamples(inputExamples): _*)

  val evaluationContext = ctx
  
  fine("building codegen evaluator with params " + params + " and program: " + program)
  lazy val _evaluator = new CodeGenEvaluator(evaluationContext, program, params)
  override def getEvaluator = _evaluator
  
  def transformExamples(examples: Seq[Example]) =
    examples.map(
      ex => {
        val map = ex.map
	    for(id <- tfd.params.map(_.id)) yield
	      map(id)
      }
    )
  
  def compile(expr: Expr, ids: Seq[Identifier]) = {
    finest("Compiling expr: " + expr + " for ids: " + ids)
    // this get is dubious
    StopwatchCollections.get("Compilation").newStopwatch profile getEvaluator.compile(expr, ids).get
  }
    
  val candidateClosures = candidates.map(cand => compile(cand.prepareExpression, tfd.params.map(_.id)))
  
  override def evaluate(candidateInd: Int, exampleInd: Int) = {
    val closure = candidateClosures(candidateInd)    
    
    finer("Index evaluate candidate [%d]%s, for [%d]%s.".format(
      candidateInd, candidates(candidateInd).prepareExpression, exampleInd, examples(exampleInd)
	))
    
    evaluate(closure, _examples(exampleInd))
  } 
  
  override def addExamples(newExamples: Seq[Example]) = {
    super.addExamples(newExamples)
    _examples ++= transformExamples(examples)
  }
  
  def evaluate(expr: Expr, args: Seq[Expr]) {
    fine("to evaluate: " + expr + " for: " + args)
    
    val closure = compile(expr, tfd.params.map(_.id))
    evaluate(closure, args)
  }
    
  override def evaluate(expr: Expr, mapping: Map[Identifier, Expr]) = {
    fine("to evaluate: " + expr + " for mapping: " + mapping)
    
    val closure = compile(expr, tfd.params.map(_.id))
    
    evaluate(closure, tfd.params.map(arg => mapping(arg.id)))
  }
    
  override def evaluateToResult(expr: Expr, mapping: Map[Identifier, Expr]): Result = {
    fine("to evaluate: " + expr + " for mapping: " + mapping)
    
    val closure = compile(expr, tfd.params.map(_.id))
    
    closure(tfd.params.map(arg => mapping(arg.id)))     
  }

  def evaluate(evalClosure: Seq[Expr] => Result, args: Seq[Expr]) = {
    try {
	    evalClosure(args) match {
	      case Successful(BooleanLiteral(true)) =>
	        fine("EvaluationSuccessful(true) for " + args)
	        true
	      case m =>
	        fine("Eval failed: " + m)
	        false
	    }
    } catch {
      case e: StackOverflowError =>
        fine("Eval failed: " + e)
        false        
    }
  }

  /** filter counterexamples according to an expression (precondition) */
  override def filter(prec: Expr) = {
    entering("filter(" + prec + ")")
    fine("Old counterExamples.size: " + examples.size)
    
    val closure = compile(prec, tfd.params.map(_.id))
    
    val (newTransformed, newExamples) = ((_examples zip examples) filter {
      case ((transformedExample, _)) =>
      	evaluate(closure, transformedExample)
    }).unzip
     
    _examples = newTransformed
    examples = newExamples
     
    fine("New counterExamples.size: " + examples.size)
  }

  /** count how many examples pass */
  override def countPassed(expressionToCheck: Expr) = {
    fine("expressionToCheck: " + expressionToCheck)

    val closure = compile(expressionToCheck, tfd.params.map(_.id))
    
    val (passed, failed) = (_examples zip examples).partition(
      pair => evaluate(closure, pair._1)
    )
    
    fine("(passed.size, failed.size): " + (passed.size, failed.size))
    (passed.size, passed map (_._2))
  }

}
