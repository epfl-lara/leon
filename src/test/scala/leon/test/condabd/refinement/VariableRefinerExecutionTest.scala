/* Copyright 2009-2014 EPFL, Lausanne */

package leon.test.condabd
package refinement

import scala.util.Random

import org.scalatest.FunSpec
import org.scalatest.GivenWhenThen

import leon.purescala.Definitions._
import leon.purescala.Common._
import leon.purescala.TypeTrees._
import leon.purescala.Trees._
import leon.evaluators._

import leon.synthesis.condabd.insynth.leon._
import leon.synthesis.condabd.insynth.leon.loader._
import leon.synthesis.condabd.refinement._

import util.Scaffold

class VariableRefinerExecutionTest extends FunSpec with GivenWhenThen {

  import Scaffold._
  import RefinementExamples._

  val lesynthTestDir = "testcases/condabd/test/lesynth/"  
      
  describe("A variable execution refiner with list ADT on insertion sort") {
    
    it("should refine if condition is isSorted()") {
      
      for ( (sctx, funDef, problem) <- forFile(lesynthTestDir + "/InsertionSortInsert.scala")) {
        val program = sctx.program
        val solver = sctx.solverFactory
        val reporter = sctx.reporter
        val codeGenEval = new CodeGenEvaluator(sctx.context, sctx.program)
        
        val loader = new LeonLoader(program, problem.as, false)
        val allDeclarations = loader.load
        val (directSubclassMap, listAbstractClass, classMap) = buildClassMap(program)
                
        val isSorted = 
          program.definedFunctions.find { 
            _.id.name == "isSorted"
          } match {
            case Some(found) => (x: Expr) => FunctionInvocation(found.typed, Seq(x))
            case _ => fail("could not extract isSorted"); null
          }
            
        val listVal = funDef.params.find(_.id.name == "l").get.toVariable
        val listLeonDeclaration = LeonDeclaration(
          ImmediateExpression( "tempVar", listVal ), 
          TypeTransformer(listAbstractClass), listAbstractClass
        )
        
        Given("a VariableRefinerExecution")
        val declarations = List(listLeonDeclaration)
        val variableRefiner = new VariableRefinerExecution(
          declarations, classMap
        )
        
        val res = variableRefiner.refine(
            isSorted(listVal),
            BooleanLiteral(true),
            declarations,
            codeGenEval
          )
          
        Then("declarations should be updated accordingly")
        expectResult((true, declarations.size + 2)) {
          (res._1, res._2.size)
        }
        
        withClue(declarations.toString) {
          assert {
            res._2.exists(_.leonType.toString contains "Cons")
          }
        }
        
        And("after 2nd consequtive call, nothing should happen")   
        expectResult((false, res._2)) {
          val res2 = variableRefiner.refine(
            isSorted(listVal),
            BooleanLiteral(true),
            res._2,
            codeGenEval
          )
          (res2._1, res2._2)
        }
      }
    }
  }
    
  describe("A variable execution refiner with list ADT on lists") {

    it("should refine if condition is isEmpty()") {
      
      for ( (sctx, funDef, problem) <- forFile(lesynthTestDir + "/ListConcatWithEmpty.scala")) {
        val program = sctx.program
        val solver = sctx.solverFactory
        val reporter = sctx.reporter
        val codeGenEval = new CodeGenEvaluator(sctx.context, sctx.program)
        
        val loader = new LeonLoader(program, problem.as, false)
        val allDeclarations = loader.load
        val (directSubclassMap, listAbstractClass, classMap) = buildClassMap(program)
                
        val isEmpty = 
          program.definedFunctions.find { 
            _.id.name == "isEmpty"
          } match {
            case Some(found) => (x: Expr) => FunctionInvocation(found.typed, Seq(x))
            case _ => fail("could not extract isEmpty"); null
          }
            
        val isEmptyBad = 
          program.definedFunctions.find { 
            _.id.name == "isEmptyBad"
          } match {
            case Some(found) => (x: Expr) => FunctionInvocation(found.typed, Seq(x))
            case _ => fail("could not extract isEmpty"); null
          }
          
        val listVal = funDef.params.head.toVariable
        val listLeonDeclaration = LeonDeclaration(
          ImmediateExpression( "tempVar", listVal ), 
          TypeTransformer(listAbstractClass), listAbstractClass
        )
        
        Given("a VariableRefinerExecution")
        val declarations = List(listLeonDeclaration)
        val variableRefiner = new VariableRefinerExecution(
          declarations, classMap
        )
        
        val res = variableRefiner.refine(
            isEmpty(listVal),
            BooleanLiteral(true),
            declarations,
            codeGenEval
          )
          
        Then("declarations should be updated accordingly")
        expectResult((true, declarations.size + 2)) {
          (res._1, res._2.size)
        }
        
        withClue(declarations.toString) {
          assert {
            res._2.exists(_.leonType.toString contains "Cons")
          }
        }
        
        And("after 2nd consequtive call, nothing should happen")   
        expectResult((false, res._2)) {
          val res2 = variableRefiner.refine(
            isEmpty(listVal),
            BooleanLiteral(true),
            res._2,
            codeGenEval
          )
          (res2._1, res2._2)
        }
      }
    }
    
    it("should refine list to Cons if condition is hasContent()") {
      
      for ( (sctx, funDef, problem) <- forFile(lesynthTestDir + "/ListConcatWithEmpty.scala")) {
        val program = sctx.program
        val solver = sctx.solverFactory
        val reporter = sctx.reporter
        val codeGenEval = new CodeGenEvaluator(sctx.context, sctx.program)
        
        val loader = new LeonLoader(program, problem.as, false)
        val allDeclarations = loader.load
//        val inSynth = new InSynth(loader, true)
//        val allDeclarations = inSynth.getCurrentBuilder.getAllDeclarations
        val (directSubclassMap, listAbstractClass, classMap) = buildClassMap(program)
                
        val hasContent = 
          program.definedFunctions.find { 
            _.id.name == "hasContent"
          } match {
            case Some(found) => (x: Expr) => FunctionInvocation(found.typed, Seq(x))
            case _ => fail("could not extract hasContent"); null
          }
          
        val listVal = funDef.params.head.toVariable
        val listLeonDeclaration = LeonDeclaration(
          ImmediateExpression( "tempVar", listVal ), 
          TypeTransformer(listAbstractClass), listAbstractClass
        )
        
        Given("a VariableRefinerExecution")
        val declarations = List(listLeonDeclaration)
        val variableRefiner = new VariableRefinerExecution(
          declarations, classMap
        )
        
        val condition = Not(hasContent(listVal))
        
        val res = variableRefiner.refine(
            condition,
            BooleanLiteral(true),
            declarations,
            codeGenEval
          )
          
        Then("declarations should be updated accordingly")
        expectResult((true, declarations.size + 2)) {
          (res._1, res._2.size)
        }
        
        withClue(declarations.toString) {
          assert {
            res._2.exists(_.leonType.toString contains "Cons")
          }
        }
        
        And("after 2nd consequtive call, nothing should happen")   
        expectResult((false, res._2)) {
          val res2 = variableRefiner.refine(
            condition,
            BooleanLiteral(true),
            res._2,
            codeGenEval
          )
          (res2._1, res2._2)
        }
      }
    }
    
    it("should not refine if condition is isEmptyBad()") {
      
      for ( (sctx, funDef, problem) <- forFile(lesynthTestDir + "/ListConcatWithEmpty.scala")) {
        val program = sctx.program
        val solver = sctx.solverFactory
        val reporter = sctx.reporter
        val codeGenEval = new CodeGenEvaluator(sctx.context, sctx.program)
        
        val loader = new LeonLoader(program, problem.as, false)
        val allDeclarations = loader.load
//        val inSynth = new InSynth(loader, true)
//        val allDeclarations = inSynth.getCurrentBuilder.getAllDeclarations
        val (directSubclassMap, listAbstractClass, classMap) = buildClassMap(program)
                
        val isEmpty = 
          program.definedFunctions.find { 
            _.id.name == "isEmpty"
          } match {
            case Some(found) => (x: Expr) => FunctionInvocation(found.typed, Seq(x))
            case _ => fail("could not extract isEmpty"); null
          }
            
        val isEmptyBad = 
          program.definedFunctions.find { 
            _.id.name == "isEmptyBad"
          } match {
            case Some(found) => (x: Expr) => FunctionInvocation(found.typed, Seq(x))
            case _ => fail("could not extract isEmpty"); null
          }
          
        val listVal = funDef.params.head.toVariable
        val listLeonDeclaration = LeonDeclaration(
          ImmediateExpression( "tempVar", listVal ), 
          TypeTransformer(listAbstractClass), listAbstractClass
        )
        
        Given("a VariableRefinerExecution")
        val declarations = List(listLeonDeclaration)
        val variableRefiner = new VariableRefinerExecution(
          declarations, classMap
        )
        
        val res = variableRefiner.refine(
            isEmptyBad(listVal),
            BooleanLiteral(true),
            declarations,
            codeGenEval
          )
        
        Then("declarations should not be updated")   
        expectResult((false, res._2)) {
          val res2 = variableRefiner.refine(
            isEmptyBad(listVal),
            BooleanLiteral(true),
            res._2,
            codeGenEval
          )
          (res2._1, res2._2)
        }
      }
    }
    
  }
  
}
