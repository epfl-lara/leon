package lesynth

import scala.util.Random

import org.scalatest.FunSpec
import org.scalatest.GivenWhenThen

import leon.purescala.Definitions._
import leon.purescala.Common._
import leon.purescala.TypeTrees._
import leon.purescala.Trees._

import insynth._
import insynth.leon._
import insynth.leon.loader._

import lesynth.refinement._

import lesynth.util._

class VariableSolverRefinerTest extends FunSpec with GivenWhenThen {    
  
  import Scaffold._
  import TestConfig._
      
  describe("A variable solver refiner with list ADT") {
    
    it("should refine if condition is isEmpty()") {
      
      for ( (sctx, funDef, problem) <- forFile(lesynthTestDir + "refinement/ListConcatWithEmpty.scala")) {
        val program = sctx.program
        val solver = sctx.solver
        
		    val hole = Hole(funDef.getBody.getType)
		    val loader = new LeonLoader(program, hole, problem.as, false)
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
        
	      given("a VariableSolverRefiner")
	      val declarations = List(listLeonDeclaration)
	      val variableRefiner = new VariableSolverRefiner(
	        directSubclassMap, declarations, classMap, solver
	      )
		    
	      val res = variableRefiner.checkRefinements(
        		isEmpty(listVal),
        		isEmpty(listVal),
        		declarations
      		)
      		
	      then("declarations should be updated accordingly")
		    expect((true, declarations.size)) {
      		(res._1, res._2.size)
	      }
		    
	      and("after 2nd consequtive call, nothing should happen")   
		    expect((false, res._2)) {
	        val res2 = variableRefiner.checkRefinements(
        		isEmpty(listVal),
        		isEmpty(listVal),
        		res._2
      		)
      		(res2._1, res2._2)
	      }
      }
    }
    
    it("should refine list to Cons if condition is hasContent()") {
      
      for ( (sctx, funDef, problem) <- forFile(lesynthTestDir + "refinement/ListConcatWithEmpty.scala")) {
        val program = sctx.program
        val solver = sctx.solver
        
		    val hole = Hole(funDef.getBody.getType)
		    val loader = new LeonLoader(program, hole, problem.as, false)
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
        
	      given("a VariableSolverRefiner")
	      val declarations = List(listLeonDeclaration)
	      val variableRefiner = new VariableSolverRefiner(
	        directSubclassMap, declarations, classMap, solver
	      )
		    
	      val res = variableRefiner.checkRefinements(
        		hasContent(listVal),
        		hasContent(listVal),
        		declarations
      		)
      		
	      then("declarations should be updated accordingly")
		    expect((true, declarations.size + 2)) {
      		(res._1, res._2.size)
	      }
		    
	      and("after 2nd consequtive call, nothing should happen")   
		    expect((false, res._2)) {
	        val res2 = variableRefiner.checkRefinements(
        		hasContent(listVal),
        		hasContent(listVal),
        		res._2
      		)
      		(res2._1, res2._2)
	      }
      }
    }
    
    it("should not refine if condition is isEmptyBad()") {
      
      for ( (sctx, funDef, problem) <- forFile(lesynthTestDir + "refinement/ListConcatWithEmpty.scala")) {
        val program = sctx.program
        val solver = sctx.solver
        
		    val hole = Hole(funDef.getBody.getType)
		    val loader = new LeonLoader(program, hole, problem.as, false)
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
        
	      given("a VariableSolverRefiner")
	      val declarations = List(listLeonDeclaration)
	      val variableRefiner = new VariableSolverRefiner(
	        directSubclassMap, declarations, classMap, solver
	      )
		    
	      val res = variableRefiner.checkRefinements(
        		isEmptyBad(listVal),
        		isEmptyBad(listVal),
        		declarations
      		)
		    
	      then("declarations should not be updated")   
		    expect((false, res._2)) {
	        val res2 = variableRefiner.checkRefinements(
        		isEmptyBad(listVal),
        		isEmptyBad(listVal),
        		res._2
      		)
      		(res2._1, res2._2)
	      }
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