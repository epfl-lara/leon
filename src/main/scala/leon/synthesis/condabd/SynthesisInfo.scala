package leon.synthesis.condabd

import leon.StopwatchCollections

/**
 * Contains information about the synthesis process
 */
class SynthesisInfo {

  import SynthesisInfo.Action

  // synthesis information
  private var _numberOfEnumeratedExpressions: Long = 0
  def numberOfEnumeratedExpressions = _numberOfEnumeratedExpressions
  def numberOfEnumeratedExpressions_=(numberOfEnumeratedExpressionsIn: Long) =
  	_numberOfEnumeratedExpressions = numberOfEnumeratedExpressionsIn
  	
  private var _iterations: Int = 0
  def iterations = _iterations
  def iterations_=(iterationsIn: Int) =
  	_iterations = iterationsIn
  
  // times
  private var times = new Array[Long](Action.values.size)
  private var startTimes = new Array[Long](Action.values.size)
  private var lastTimes = new Array[Long](Action.values.size)
  
  private var lastAction: Action.Action = Action.Evaluation
  
  def getTime(a: Action.Action) = times(a.id)
  
  def start(a: Action.Action) = {
    lastAction = a
    startTimes(a.id) = System.currentTimeMillis()
  }
  
  def end: Unit = end(lastAction)
  
  def end(a: Action.Action) = {
    lastAction = a
    lastTimes(a.id) = System.currentTimeMillis() - startTimes(a.id)
    times(a.id) += lastTimes(a.id)
  }
  
  def end[T](returnValue: => T): T = {
    val result = returnValue
    end
    result
  }
  
  def last(a: Action.Action) = lastTimes(a.id)
  
  def last: Long = last(lastAction)
  
  def profile[T](a: Action.Action)(block: => T): T = {
    lastAction = a
    startTimes(a.id) = System.currentTimeMillis()
    val result = block    // call-by-name
    lastTimes(a.id) = System.currentTimeMillis() - startTimes(a.id)
    times(a.id) += lastTimes(a.id)
    result
  }
  
}

object SynthesisInfo {
  object Action extends Enumeration {
  	type Action = Value
  	val Synthesis, 
  		Verification, Generation, Evaluation = Value
//  		VerificationBranch, VerificationCondition,
//  		EvaluationGeneration, EvaluationBranch, EvaluationCondition,
//  		VerificationCounterExampleGen 
//  		= Value
  }		
}