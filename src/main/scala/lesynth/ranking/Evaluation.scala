package lesynth
package ranking

import lesynth.evaluation._

case class Evaluation(exampleRunner: ExampleRunner) {
  
  // keep track of which examples to evaluate next
  var nextExamples: Map[Int, Int] = Map().withDefaultValue(0)
  
  def getNumberOfEvaluations(ind: Int) = nextExamples(ind)
  
  // keep track of evaluation results
  var evaluations = Map[Int, Array[Boolean]]()
  
  def getEvaluationVector(ind: Int) =
    (evaluations(ind), nextExamples(ind))
  
  def numberOfExamples = exampleRunner.examples.size
    
  def evaluate(exprInd: Int) = {     
    numberOfEvaluationCalls += 1
    
    // get next example index and update
    val nextExample = nextExamples(exprInd)//OrElse(exprInd, 0)
    if (nextExample >= numberOfExamples) throw new RuntimeException("Exhausted examples for " + exprInd)
    nextExamples += (exprInd -> (nextExample + 1))
      
    val result = exampleRunner.evaluate(exprInd, nextExample)
    
    // update evaluation results
    val evalArray = evaluations.getOrElse(exprInd, Array.ofDim[Boolean](numberOfExamples))
    evalArray(nextExample) = result
    evaluations += (exprInd -> evalArray)
    
    result
  }
  
  // for measurements
  var numberOfEvaluationCalls = 0
  def getEfficiencyRatio = numberOfEvaluationCalls.toFloat / (numberOfExamples * evaluations.size)
  
//  def evaluate(expr: Int, exampleInd: Int) = {
//    val nextExample = nextExamples.getOrElse(expr, 0)
//    assert(exampleInd <= nextExample)
//    
//    if (exampleInd >= nextExample) {
//	    nextExamples += (expr -> (nextExample + 1))	        
//	    val example = examples(nextExample)   
//	    val result = example(expr)
//	    val evalArray = evaluations.getOrElse(expr, Array.ofDim[Boolean](examples.size))
//	    evalArray(nextExample) = result
//	    evaluations += (expr -> evalArray)
//	    result   
//    } else {
//      assert(evaluations.contains(expr))
//      evaluations.get(expr).get(exampleInd)
//    }
//  }
  
//  def evalAvailable(expr: Int) = {    
//    val nextExample = nextExamples.getOrElse(expr, 0)
//    if (nextExample >= examples.size) false
//    else true
//  }
    
}