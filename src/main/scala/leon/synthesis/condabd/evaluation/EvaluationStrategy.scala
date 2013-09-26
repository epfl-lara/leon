package leon.synthesis.condabd
package evaluation

import leon._
import leon.evaluators._
import leon.evaluators.EvaluationResults._
import leon.purescala.Trees._
import leon.purescala.Definitions.{ FunDef, VarDecl, Program, ObjectDef }
import leon.purescala.Common.{ Identifier, FreshIdentifier }
import leon.purescala.TreeOps
import leon.codegen.CodeGenEvalParams

import insynth.reconstruction.Output
import _root_.insynth.util.logging._

import ranking._
import examples._

trait EvaluationStrategy extends HasLogger {
  def getRanker(candidatePairs: IndexedSeq[(Output)], bodyBuilder: (Expr) => Expr, inputExamples: Seq[Example]): Ranker
  
  def getExampleRunner: ExampleRunner
  
  def getEvaluation: Evaluation
  
  protected def logCounts(candidates: IndexedSeq[Candidate], inputExamples: Seq[Example]) {    
    // printing candidates and pass counts        
    fine("Ranking with examples: " + inputExamples.mkString(", "))
    fine( {
      val logString = ((candidates.zipWithIndex) map {
        case (cand: Candidate, ind: Int) => {
        	val result = getExampleRunner.countPassed(cand.prepareExpression)
          ind + ": snippet is " + cand.getExpr +
          " pass count is " + result._1 +"/" + inputExamples.size + " (" + result._2.mkString(", ") + ")"
        }
      }).mkString("\n")
      logString
    })
  }
  
}

case class DefaultEvaluationStrategy(program: Program, funDef: FunDef, ctx: LeonContext,  
  maxSteps: Int = 2000) extends EvaluationStrategy with HasLogger {
  
  var exampleRunner: ExampleRunner = _
  
  var evaluation: Evaluation = _
  
  override def getRanker(candidatePairs: IndexedSeq[Output], bodyBuilder: (Expr) => Expr, inputExamples: Seq[Example]) = {
    
    val candidates = Candidate.makeDefaultCandidates(candidatePairs, bodyBuilder, funDef) 
        
    exampleRunner = DefaultExampleRunner(program, funDef, ctx, candidates, inputExamples)
    
    logCounts(candidates, inputExamples)
    
    // printing candidates and pass counts        
    fine("Ranking with examples: " + inputExamples.mkString(", "))
    fine( {
      val logString = ((candidates.zipWithIndex) map {
        case (cand: Candidate, ind: Int) => {
        	val result = exampleRunner.countPassed(cand.prepareExpression)
          ind + ": snippet is " + cand.expr +
          " pass count is " + result._1 + " (" + result._2.mkString(", ") + ")"
        }
      }).mkString("\n")
      logString
    })
    
    evaluation = Evaluation(exampleRunner)
    
    new Ranker(candidates, evaluation)
  }
  
  override def getExampleRunner = exampleRunner
  
  override def getEvaluation = evaluation
}

case class CodeGenEvaluationStrategy(program: Program, funDef: FunDef, ctx: LeonContext,  
  maxSteps: Int = 200) extends EvaluationStrategy with HasLogger {
  
  var exampleRunner: ExampleRunner = _
  
  var evaluation: Evaluation = _
  
  override def getRanker(candidatePairs: IndexedSeq[Output], bodyBuilder: (Expr) => Expr, inputExamples: Seq[Example]) = {
    
    val candidates = Candidate.makeCodeGenCandidates(candidatePairs, bodyBuilder, funDef) 
    
	val newProgram = program.copy(mainObject = program.mainObject.copy(defs = program.mainObject.defs ++ candidates.map(_.newFunDef)))
	
	finest("New program looks like: " + newProgram)
	finest("Candidates look like: " + candidates.map(_.prepareExpression).mkString("\n"))
        
		val params = CodeGenEvalParams(maxFunctionInvocations = maxSteps, checkContracts = true)
	
    exampleRunner = CodeGenExampleRunner(newProgram, funDef, ctx, candidates, inputExamples, params)
        
    logCounts(candidates, inputExamples)
    
    evaluation = Evaluation(exampleRunner)
    
    new Ranker(candidates, evaluation)
  }
  
  override def getExampleRunner = exampleRunner
  
  override def getEvaluation = evaluation
}