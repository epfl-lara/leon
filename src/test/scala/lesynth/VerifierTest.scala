package lesynth

import org.junit.Assert._
import org.junit._
import org.scalatest._
import org.scalatest.matchers._

import insynth.leon.loader.LeonLoader

import _root_.leon.purescala._
import _root_.leon.evaluators._
import _root_.leon.solvers._

import util._

class VerifierTest extends FunSpec {

  import Utils._
  import Scaffold._
  import TestConfig._
	
	describe("Concrete verifier: ") {    
    val testCaseFileName = lesynthTestDir + "/verifier/ListConcat.scala"
    
    val problems = forFile(testCaseFileName)
    assert(problems.size == 1)
      
  	for ((sctx, funDef, problem) <- problems) {
  	  
  	  val timeoutSolver = new TimeoutSolver(sctx.solver, 2000L)
  	
  	  describe("A Verifier") {
  	    it("should verify first correct concat body") {		  	  
		  	  funDef.body = getFunDefByName(sctx.program, "goodConcat1").body
		  	  
		  	  val verifier = new Verifier(timeoutSolver.getNewSolver, problem)
		  	  
		  	  verifier.analyzeFunction(funDef)._1
  	    }  	    
  	    
  	    it("should verify 2nd correct concat body") {		  	  
		  	  funDef.body = getFunDefByName(sctx.program, "goodConcat2").body
		  	  
		  	  val verifier = new Verifier(timeoutSolver.getNewSolver, problem)
		  	  
		  	  verifier.analyzeFunction(funDef)._1
  	    }  	    
  	    
  	    it("should not verify an incorrect concat body") {
		  	  funDef.body = getFunDefByName(sctx.program, "badConcat1").body
		  	  
		  	  val verifier = new Verifier(timeoutSolver.getNewSolver, problem)
		  	  
		  	  ! verifier.analyzeFunction(funDef)._1
  	    }
  	  }
  	}				
	}
  
	describe("Relaxed verifier: ") {    
    val testCaseFileName = lesynthTestDir + "/verifier/BinarySearchTree.scala"
    
    val problems = forFile(testCaseFileName)
    assert(problems.size == 1)
      
  	for ((sctx, funDef, problem) <- problems) {
  	  
  	  val timeoutSolver = new TimeoutSolver(sctx.solver, 1000L)
  	
  	  describe("A RelaxedVerifier on BST") {
  	    it("should verify a correct member body") {		
		  	  funDef.body = getFunDefByName(sctx.program, "goodMember").body  	  
		  	  
		  	  val verifier = new RelaxedVerifier(timeoutSolver.getNewSolver, problem)
		  	  
		  	  verifier.analyzeFunction(funDef)._1
  	    }  	    
  	      	    
  	    it("should not verify an incorrect member body") {
		  	  funDef.body = getFunDefByName(sctx.program, "badMember").body
		  	  
		  	  val verifier = new Verifier(timeoutSolver.getNewSolver, problem)
		  	  
		  	  verifier.analyzeFunction(funDef)._1
  	    }
  	  }
  	}				
	}
  
}
