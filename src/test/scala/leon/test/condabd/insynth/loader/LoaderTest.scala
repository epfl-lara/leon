package leon.test.condabd
package insynth
package loader

import util._

import leon.synthesis.condabd.insynth.leon._
import leon.synthesis.condabd.insynth.leon.loader._

import _root_.leon.purescala.Definitions._
import _root_.leon.purescala.Common._
import _root_.leon.purescala.TypeTrees._
import _root_.leon.purescala.Trees.{ Variable => LeonVariable, _ }

import org.junit.{ Test, Ignore }
import org.junit.Assert._
import org.scalatest.junit.JUnitSuite

class LoaderTest extends JUnitSuite {

  import Scaffold._

	val insynthTestDir = "testcases/condabd/test"
  val testDir = insynthTestDir + "/insynth/"
    
  @Test
  def testAddresses {
    val fileName = testDir + "Addresses.scala"
  	
    for ((sctx, funDef, problem) <- forFile(fileName)) {
      val program = sctx.program
      val arguments = funDef.args.map(_.id)

      assertEquals(1, problem.xs.size)
      val resultVariable = problem.xs.head
      val varsInScope = problem.as

	    val loader = new LeonLoader(program, varsInScope, false)
	    
      val allDeclarations = loader.load.map(d => (d.getSimpleName, d.leonType.toString)).toSet

      val expectedDeclarations = Set(
        ("AddressBook", "(List, List) => AddressBook"),
        ("[Cons=>List]", "Cons => List"),
        ("pers", "AddressBook => List"),
        ("makeAddressBook", "List => AddressBook"),
        ("addToPers", "(AddressBook, Address) => AddressBook"),
        ("addToBusiness", "(AddressBook, Address) => AddressBook"),
        ("l", "List"),
        ("tail", "Cons => List"),
        ("a", "Cons => Address")
  		)
  		
		  assertTrue(
	      "Expected:\n" + expectedDeclarations.mkString("\n") + "\nFound:\n" + allDeclarations.mkString("\n"),
	      expectedDeclarations.subsetOf(allDeclarations)	      
      )
    }
  }
 
  @Test
  def testListConcat {
    val fileName = testDir + "ListConcat.scala"
  	
    for ((sctx, funDef, problem) <- forFile(fileName)) {
      val program = sctx.program
      val arguments = funDef.args.map(_.id)

      assertEquals(1, problem.xs.size)
      val resultVariable = problem.xs.head
      val varsInScope = problem.as

	    val loader = new LeonLoader(program, varsInScope, false)
	    
      val allDeclarations = loader.load.map(d => (d.getSimpleName, d.leonType.toString)).toSet

      val expectedDeclarations = Set(
        ("[Nil=>List]", "Nil => List"),
        ("[Cons=>List]", "Cons => List"),
        ("concat", "(List, List) => List"),
        ("l1", "List"),
        ("l2", "List"),
        ("tail", "Cons => List"),
        ("head", "Cons => Int")
  		)
  		
		  assertTrue(
	      "Expected:\n" + expectedDeclarations.mkString("\n") + "\nFound:\n" + allDeclarations.mkString("\n"),
	      expectedDeclarations.subsetOf(allDeclarations)	      
      )
    }
  } 
  
  @Test
  def testAddressesWithAddition {
    val fileName = testDir + "AddressesWithAddition.scala"
  	
    for ((sctx, funDef, problem) <- forFile(fileName)) {
      val program = sctx.program
      val arguments = funDef.args.map(_.id)

      assertEquals(1, problem.xs.size)
      val resultVariable = problem.xs.head
      val varsInScope = funDef.args.map(_.id).toList //problem.as)
      assertTrue(varsInScope.size >= 3)

	    val loader = new LeonLoader(program, varsInScope, false)
	    
      val allDeclarations = loader.load.map(d => (d.getSimpleName, d.leonType.toString)).toSet

      val expectedDeclarations = Set(
        ("AddressBook", "(List, List) => AddressBook"),
        ("[Cons=>List]", "Cons => List"),
        ("pers", "AddressBook => List"),
        ("addToPers", "(AddressBook, Address) => AddressBook"),
        ("addToBusiness", "(AddressBook, Address) => AddressBook"),
        ("l", "List"),
        ("tail", "Cons => List"),
        ("a", "Cons => Address"),
        ("x", "Int"),
        ("y", "Boolean")
  		)
  		
		  assertTrue(
	      "Expected:\n" + expectedDeclarations.mkString("\n") + "\nFound:\n" + allDeclarations.mkString("\n"),
	      expectedDeclarations.subsetOf(allDeclarations)	      
      )
    }
  } 

}