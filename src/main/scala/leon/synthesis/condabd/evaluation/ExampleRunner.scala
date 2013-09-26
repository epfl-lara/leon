package leon.synthesis.condabd
package evaluation

import scala.collection.mutable.ArrayBuffer

import leon.purescala.Trees._
import leon.purescala.Common.Identifier
import leon.evaluators._
import leon.evaluators.EvaluationResults.Result

import _root_.insynth.util.logging.HasLogger

import examples.Example

abstract class ExampleRunner(inputExamples: Seq[Example]) extends HasLogger {

  private var _examples = ArrayBuffer(inputExamples: _*)
  protected def examples_=(newExamples: ArrayBuffer[Example]) = _examples = newExamples 
  def examples = _examples
  
  def addExamples(newExamples: Seq[Example]): Unit = {
    _examples ++= newExamples
  }
  
  def getEvaluator: Evaluator

  /** evaluate given expression */
  def evaluate(expr: Expr, mapping: Map[Identifier, Expr]): Boolean

  def evaluateToResult(expr: Expr, mapping: Map[Identifier, Expr]): Result 
 
  /** if the example runner knows about candidates and input examples, run by their indexes */
  def evaluate(candidateInd: Int, exampleInd: Int): Boolean
  
  /** filter counterexamples according to an expression (precondition) */
  def filter(prec: Expr): Unit 

  /** count how many examples pass */
  def countPassed(expressionToCheck: Expr): (Int, Seq[Example]) 

}