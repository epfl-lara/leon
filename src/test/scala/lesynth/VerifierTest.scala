package lesynth

import org.junit.Assert._
import org.junit._
import org.scalatest._
import org.scalatest.matchers._

import insynth.leon.loader.LeonLoader

import _root_.leon.purescala._
import _root_.leon.evaluators._
import _root_.leon.solvers._
import _root_.leon.purescala.Trees._
import leon.purescala.Common._
import leon.purescala.Definitions._
import leon.synthesis.Problem

import _root_.util._

class VerifierTest extends FunSpec {

  import Utils._
  import Scaffold._

	val lesynthTestDir = "testcases/condabd/test/lesynth"
	  
  def getPostconditionFunction(problem: Problem) = {
    (list: Iterable[Identifier]) => {
      (problem.phi /: list) {
        case ((res, newId)) =>
        	(res /: problem.as.find(_.name == newId.name)) {
        	  case ((res, oldId)) =>
        	    TreeOps.replace(Map(Variable(oldId) -> Variable(newId)), res)
        	}
      }
    }
  }
	
	describe("Concrete verifier: ") {    
    val testCaseFileName = lesynthTestDir + "/ListConcatVerifierTest.scala"
    
    val problems = forFile(testCaseFileName)
    assert(problems.size == 1)
      
  	for ((sctx, funDef, problem) <- problems) {
  	  
  	  val timeoutSolver = sctx.solverFactory.withTimeout(2000L)
  	  
		  val getNewPostcondition = getPostconditionFunction(problem)
  	
  	  describe("A Verifier") {
  	    it("should verify first correct concat body") {		  	  
  	      val newFunDef = getFunDefByName(sctx.program, "goodConcat1")
		  	  funDef.body = newFunDef.body

		  	  expectResult(1) { problem.xs.size }
		  	  funDef.postcondition = Some((problem.xs.head, getNewPostcondition(newFunDef.args.map(_.id))))
		  	  funDef.precondition = Some(BooleanLiteral(true)) 
		  	  
		  	  val verifier = new Verifier(timeoutSolver, problem)
		  	  
		  	  assert( verifier.analyzeFunction(funDef)._1 )
  	    }  	    
  	    
  	    it("should verify 2nd correct concat body") {		  	  
  	      val newFunDef = getFunDefByName(sctx.program, "goodConcat2")
		  	  funDef.body = newFunDef.body

		  	  expectResult(1) { problem.xs.size }
		  	  funDef.postcondition = Some((problem.xs.head, getNewPostcondition(newFunDef.args.map(_.id))))
		  	  funDef.precondition = Some(BooleanLiteral(true)) 
		  	  
		  	  val verifier = new Verifier(timeoutSolver, problem)
		  	  
		  	  assert( verifier.analyzeFunction(funDef)._1 )
  	    }  	    
  	    
  	    it("should not verify an incorrect concat body") {
		  	  val newFunDef = getFunDefByName(sctx.program, "badConcat1")
		  	  funDef.body = newFunDef.body

		  	  expectResult(1) { problem.xs.size }
		  	  funDef.postcondition = Some((problem.xs.head, getNewPostcondition(newFunDef.args.map(_.id))))
		  	  funDef.precondition = Some(BooleanLiteral(true)) 
		  	  
		  	  val verifier = new Verifier(timeoutSolver, problem)
		  	  
		  	  assert( ! verifier.analyzeFunction(funDef)._1 )
  	    }
  	  }
  	  
  	  timeoutSolver.free
  	}
	}

  def getPreconditionFunction(problem: Problem) = {
    (list: Iterable[Identifier]) => {
      (problem.pc /: list) {
        case ((res, newId)) =>
        	(res /: problem.as.find(_.name == newId.name)) {
        	  case ((res, oldId)) =>
        	    TreeOps.replace(Map(Variable(oldId) -> Variable(newId)), res)
        	}
      }
    }
  }
  
	describe("Relaxed verifier: ") {    
    val testCaseFileName = lesynthTestDir + "/BinarySearchTree.scala"
    
    val problems = forFile(testCaseFileName)
    assert(problems.size == 1)
      
  	for ((sctx, funDef, problem) <- problems) {
  	  
  	  val timeoutSolver = sctx.solverFactory.withTimeout(1000L)
  	  
		  val getNewPostcondition = getPostconditionFunction(problem)
		  val getNewPrecondition = getPreconditionFunction(problem)
  	
  	  describe("A RelaxedVerifier on BST") {
  	    it("should verify a correct member body") {		
		  	  val newFunDef = getFunDefByName(sctx.program, "goodMember")
		  	  funDef.body = newFunDef.body

		  	  expectResult(1) { problem.xs.size }
		  	  funDef.postcondition = Some((problem.xs.head, getNewPostcondition(newFunDef.args.map(_.id))))
		  	  funDef.precondition = Some(getNewPrecondition(newFunDef.args.map(_.id)))
		  	  
		  	  val verifier = new RelaxedVerifier(timeoutSolver, problem)
		  	  
		  	  assert( verifier.analyzeFunction(funDef)._1 )
  	    }  	    
  	      	    
  	    it("should not verify an incorrect member body") {
		  	  val newFunDef = getFunDefByName(sctx.program, "badMember")
		  	  funDef.body = newFunDef.body

		  	  expectResult(1) { problem.xs.size }
		  	  funDef.postcondition = Some((problem.xs.head, getNewPostcondition(newFunDef.args.map(_.id))))
		  	  funDef.precondition = Some(getNewPrecondition(newFunDef.args.map(_.id)))
		  	  
		  	  val verifier = new Verifier(timeoutSolver, problem)
		  	  
		  	  assert( verifier.analyzeFunction(funDef)._1 )
  	    }
  	  }
  	  
  	  timeoutSolver.free
  	}
    
	}
  
}
