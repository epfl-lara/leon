package leon.test.condabd

import scala.util.Random

import org.scalatest.FunSpec
import org.scalatest.GivenWhenThen

import leon.purescala.Definitions._
import leon.purescala.Common._
import leon.purescala.TypeTrees._
import leon.purescala.Trees._

import insynth._
import leon.synthesis.condabd.insynth.leon._
import leon.synthesis.condabd.insynth.leon.loader._
import leon.synthesis.condabd.refinement._

import util._

class VariableSolverRefinerTest extends FunSpec with GivenWhenThen {

  import Scaffold._

	val lesynthTestDir = "testcases/condabd/test/lesynth/"  
      
  describe("A variable solver refiner with list ADT") {
    
    it("should refine if condition is isEmpty()") {
      
      for ( (sctx, funDef, problem) <- forFile(lesynthTestDir + "/ListConcatWithEmpty.scala")) {
        val program = sctx.program
        val solver = sctx.solverFactory
        val reporter = sctx.reporter
        
		    val loader = new LeonLoader(program, problem.as, false)
        val allDeclarations = loader.load
//		    val inSynth = new InSynth(loader, true)
//		    val allDeclarations = inSynth.getCurrentBuilder.getAllDeclarations
      	val (directSubclassMap, listAbstractClass, classMap) = buildClassMap(program)
		    		    
			  val isEmpty = 
		      program.definedFunctions.find { 
			      _.id.name == "isEmpty"
			    } match {
			      case Some(found) => (x: Expr) => FunctionInvocation(found, Seq(x))
			      case _ => fail("could not extract isEmpty"); null
			    }
				    
			  val isEmptyBad = 
		      program.definedFunctions.find { 
			      _.id.name == "isEmptyBad"
			    } match {
			      case Some(found) => (x: Expr) => FunctionInvocation(found, Seq(x))
			      case _ => fail("could not extract isEmpty"); null
			    }
			    
		    val listVal = funDef.args.head.toVariable
			  val listLeonDeclaration = LeonDeclaration(
			    ImmediateExpression( "tempVar", listVal ), 
			    TypeTransformer(listAbstractClass), listAbstractClass
			  )
        
	      Given("a VariableSolverRefiner")
	      val declarations = List(listLeonDeclaration)
	      val variableRefiner = new VariableSolverRefiner(
	        directSubclassMap, declarations, classMap, solver, reporter
	      )
		    
	      val res = variableRefiner.checkRefinements(
        		isEmpty(listVal),
        		isEmpty(listVal),
        		declarations
      		)
      		
	      Then("declarations should be updated accordingly")
		    expectResult((true, declarations.size)) {
      		(res._1, res._2.size)
	      }
		    
	      And("after 2nd consequtive call, nothing should happen")   
		    expectResult((false, res._2)) {
	        val res2 = variableRefiner.checkRefinements(
        		isEmpty(listVal),
        		isEmpty(listVal),
        		res._2
      		)
      		(res2._1, res2._2)
	      }

        solver.free()
      }
    }
    
    it("should refine list to Cons if condition is hasContent()") {
      
      for ( (sctx, funDef, problem) <- forFile(lesynthTestDir + "/ListConcatWithEmpty.scala")) {
        val program = sctx.program
        val solver = sctx.solverFactory
        val reporter = sctx.reporter
        
		    val loader = new LeonLoader(program, problem.as, false)
        val allDeclarations = loader.load
//		    val inSynth = new InSynth(loader, true)
//		    val allDeclarations = inSynth.getCurrentBuilder.getAllDeclarations
      	val (directSubclassMap, listAbstractClass, classMap) = buildClassMap(program)
		    		    
			  val hasContent = 
		      program.definedFunctions.find { 
			      _.id.name == "hasContent"
			    } match {
			      case Some(found) => (x: Expr) => FunctionInvocation(found, Seq(x))
			      case _ => fail("could not extract hasContent"); null
			    }
			    
		    val listVal = funDef.args.head.toVariable
			  val listLeonDeclaration = LeonDeclaration(
			    ImmediateExpression( "tempVar", listVal ), 
			    TypeTransformer(listAbstractClass), listAbstractClass
			  )
        
	      Given("a VariableSolverRefiner")
	      val declarations = List(listLeonDeclaration)
	      val variableRefiner = new VariableSolverRefiner(
	        directSubclassMap, declarations, classMap, solver, reporter
	      )
		    
	      val res = variableRefiner.checkRefinements(
        		hasContent(listVal),
        		hasContent(listVal),
        		declarations
      		)
      		
	      Then("declarations should be updated accordingly")
		    expectResult((true, declarations.size + 2)) {
      		(res._1, res._2.size)
	      }
		    
	      And("after 2nd consequtive call, nothing should happen")   
		    expectResult((false, res._2)) {
	        val res2 = variableRefiner.checkRefinements(
        		hasContent(listVal),
        		hasContent(listVal),
        		res._2
      		)
      		(res2._1, res2._2)
	      }
        solver.free()
      }
    }
    
    it("should not refine if condition is isEmptyBad()") {
      
      for ( (sctx, funDef, problem) <- forFile(lesynthTestDir + "/ListConcatWithEmpty.scala")) {
        val program = sctx.program
        val solver = sctx.solverFactory
        val reporter = sctx.reporter
        
		    val loader = new LeonLoader(program, problem.as, false)
        val allDeclarations = loader.load
//		    val inSynth = new InSynth(loader, true)
//		    val allDeclarations = inSynth.getCurrentBuilder.getAllDeclarations
      	val (directSubclassMap, listAbstractClass, classMap) = buildClassMap(program)
		    		    
			  val isEmpty = 
		      program.definedFunctions.find { 
			      _.id.name == "isEmpty"
			    } match {
			      case Some(found) => (x: Expr) => FunctionInvocation(found, Seq(x))
			      case _ => fail("could not extract isEmpty"); null
			    }
				    
			  val isEmptyBad = 
		      program.definedFunctions.find { 
			      _.id.name == "isEmptyBad"
			    } match {
			      case Some(found) => (x: Expr) => FunctionInvocation(found, Seq(x))
			      case _ => fail("could not extract isEmpty"); null
			    }
			    
		    val listVal = funDef.args.head.toVariable
			  val listLeonDeclaration = LeonDeclaration(
			    ImmediateExpression( "tempVar", listVal ), 
			    TypeTransformer(listAbstractClass), listAbstractClass
			  )
        
	      Given("a VariableSolverRefiner")
	      val declarations = List(listLeonDeclaration)
	      val variableRefiner = new VariableSolverRefiner(
	        directSubclassMap, declarations, classMap, solver, reporter
	      )
		    
	      val res = variableRefiner.checkRefinements(
        		isEmptyBad(listVal),
        		isEmptyBad(listVal),
        		declarations
      		)
		    
	      Then("declarations should not be updated")   
		    expectResult((false, res._2)) {
	        val res2 = variableRefiner.checkRefinements(
        		isEmptyBad(listVal),
        		isEmptyBad(listVal),
        		res._2
      		)
      		(res2._1, res2._2)
	      }

          solver.free()
      }
    }
    
  }
  
  private def buildClassMap(program: Program) = {
	  val listAbstractClassDef = program.definedClasses.find(_.id.name == "List").
  		get.asInstanceOf[AbstractClassDef]
	  
	  val nilAbstractClassDef = program.definedClasses.find(_.id.name == "Nil").
  		get.asInstanceOf[CaseClassDef]
	  
	  val consAbstractClassDef = program.definedClasses.find(_.id.name == "Cons").
  		get.asInstanceOf[CaseClassDef]
	  	  
	  val directSubclassMap: Map[ClassType, Set[ClassType]] = Map(
	    AbstractClassType(listAbstractClassDef) ->
	    	Set(CaseClassType(nilAbstractClassDef), CaseClassType(consAbstractClassDef))
	  )
  
	  val classMap: Map[Identifier, ClassType] = Map(
	    listAbstractClassDef.id -> AbstractClassType(listAbstractClassDef),
	    nilAbstractClassDef.id -> CaseClassType(nilAbstractClassDef),
	    consAbstractClassDef.id -> CaseClassType(consAbstractClassDef)
	  )
	  
	  (directSubclassMap, AbstractClassType(listAbstractClassDef), classMap)
  }
  
}
