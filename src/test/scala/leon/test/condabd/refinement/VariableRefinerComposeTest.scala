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

class VariableRefinerComposeTest extends FunSpec with GivenWhenThen {

  import Scaffold._
  import RefinementExamples._

  val lesynthTestDir = "testcases/condabd/test/lesynth/"  
      
  describe("A variable compose(structure, exec) refiner with list ADT") {
    
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
            
        val listVal = funDef.args.find(_.id.name == "l").get.toVariable
        val listLeonDeclaration = LeonDeclaration(
          ImmediateExpression( "tempVar", listVal ), 
          TypeTransformer(listAbstractClass), listAbstractClass
        )
        
        Given("a VariableRefinerCompose")
        val declarations = List(listLeonDeclaration)
        val variableRefiner = new VariableRefinerCompose add
          new VariableRefinerStructure(
            directSubclassMap, Seq(listLeonDeclaration), classMap, reporter
          ) add    
          new VariableRefinerExecution(
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
      
  describe("A variable compose(structure) refiner with list ADT") {
    
    it("should not refine if condition is isSorted()") {
      
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
            
        val listVal = funDef.args.find(_.id.name == "l").get.toVariable
        val listLeonDeclaration = LeonDeclaration(
          ImmediateExpression( "tempVar", listVal ), 
          TypeTransformer(listAbstractClass), listAbstractClass
        )
        
        Given("a VariableRefinerCompose")
        val declarations = List(listLeonDeclaration)
        val variableRefiner = new VariableRefinerCompose add
          new VariableRefinerStructure(
            directSubclassMap, Seq(listLeonDeclaration), classMap, reporter
          )
        
        val res = variableRefiner.refine(
            isSorted(listVal),
            BooleanLiteral(true),
            declarations,
            codeGenEval
          )
          
        Then("declarations should stay the same")
        expectResult((false, declarations.size)) {
          (res._1, res._2.size)
        }        
      }
    }
    
  }
  
}
