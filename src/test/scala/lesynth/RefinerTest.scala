package lesynth

import scala.util.Random

import org.junit.Assert._
import org.junit.{ Test, Ignore, Before }

import insynth.leon.HoleFinder
import insynth.leon.loader.{ LeonLoader, HoleExtractor }
import insynth.leon._

import _root_.leon.purescala.Trees.{ Expr, Hole, IntLiteral, UnitLiteral, Variable, FunctionInvocation, And }
import _root_.leon.purescala.{ TreeOps }
import _root_.leon.purescala.Definitions.{ Program, FunDef }
import _root_.leon.evaluators._
import _root_.leon.{ LeonContext, DefaultReporter, Main }
import _root_.leon.verification.AnalysisPhase

import insynth.testutil.CommonUtils
import testutil.TestConfig

class RefinerTest {

  import TestConfig._
  import CommonUtils._
  import TreeOps._
  
  val rnd = new Random(System.currentTimeMillis())
  
  var prog: Program = _
  var hole: Hole = _
  var holeFunDef: FunDef = _
  
  var tail: UnaryReconstructionExpression = _
  var head: UnaryReconstructionExpression = _
  var nil: Expr = _
  var cons: NaryReconstructionExpression = _
  
  @Before
  def extract = {
    
    val holeFinder = new HoleFinder(lesynthTestDir + "ListOperationsHole.scala")
				
    holeFinder.extract match {
      case Some((progE, holeE)) =>
                
      prog = progE
      hole = holeE
        
      holeFunDef = new HoleExtractor(prog, hole).extractHole match {
        case Some((hfd, _)) => hfd
        case None => fail("could not extract hole"); null
      } 
		
	    val loader = new LeonLoader(prog, hole)
	    
	    tail = 
	      loader.extractFields.find { 
		      _.expression match {
		        case ure: UnaryReconstructionExpression => ure(UnitLiteral).toString.contains(".tail")
		        case _ => false
		      }
		    } match {
		      case Some(found) => found.expression.asInstanceOf[UnaryReconstructionExpression]
		      case _ => fail("could not extract tail"); null
		    }
		    
	    head = 
	      loader.extractFields.find { 
		      _.expression match {
		        case ure: UnaryReconstructionExpression => ure(UnitLiteral).toString.contains(".head")
		        case _ => false
		      }
		    } match {
		      case Some(found) => found.expression.asInstanceOf[UnaryReconstructionExpression]
		      case _ => fail("could not extract head"); null
		    }
		    
	    cons = 
	      loader.extractCaseClasses.find { 
		      _.expression match {
		        case nre: NaryReconstructionExpression => nre(List(UnitLiteral, UnitLiteral)).toString.contains("Cons")
		        case _ => false
		      }
		    } match {
		      case Some(found) => found.expression.asInstanceOf[NaryReconstructionExpression]
		      case _ => fail("could not extract cons"); null
		    }
		    
	    nil = 
	      loader.extractCaseClasses.find { 
		      _.expression match {
		        case im: ImmediateExpression => im().toString.contains("Nil")
		        case _ => false
		      }
		    } match {
		      case Some(found) => found.expression.asInstanceOf[ImmediateExpression]()
		      case _ => fail("could not extract cons"); null
		    }
		    
      case _ =>
        fail("HoleFinder could not extract hole from the program")
    }    
  }
	  
	@Test
	def testIsLess = {
		    
	    val refiner = new Refiner(prog, hole, holeFunDef)
	    import refiner.isLess
	    
	    assertEquals(2, holeFunDef.args.size)
	    
	    val variable1 = holeFunDef.args.head
	    val variable2 = holeFunDef.args(1)
	    
	    assertEquals(+1, isLess(cons(List(UnitLiteral, variable1.toVariable)), variable1))
	    assertEquals(+1, isLess(cons(List(UnitLiteral, variable1.toVariable)), variable2))
	    assertEquals(-1, isLess(tail(variable1.toVariable), variable1))
	    assertEquals(+1, isLess(head(variable1.toVariable), variable1))
	    assertEquals(0, isLess(variable1.toVariable, variable1))
	    assertEquals(1, isLess(variable1.toVariable, variable2))
	    assertEquals(1, isLess(tail(variable1.toVariable), variable2))
	    assertEquals(1, isLess(head(variable1.toVariable), variable2))
	    assertEquals(1, isLess(nil, variable2))
        
	}
  
	@Test
	def testIsCallLessBySize = {
	    
    val refiner = new Refiner(prog, hole, holeFunDef)
    import refiner.isCallAvoidableBySize
    
    assertEquals(2, holeFunDef.args.size)
    
    val arg1 = holeFunDef.args.head.toVariable
    val arg2 = holeFunDef.args(1).toVariable
    
    def makeFunctionCall(arg1: Expr, arg2: Expr) = FunctionInvocation(holeFunDef, Seq(arg1, arg2)) 
    
    assertEquals(true, isCallAvoidableBySize(makeFunctionCall(nil, nil)))
    assertEquals(true, isCallAvoidableBySize(makeFunctionCall(arg1, arg2)))
    assertEquals(true, isCallAvoidableBySize(makeFunctionCall(arg2, arg1)))
    assertEquals(false, isCallAvoidableBySize(makeFunctionCall(arg1, tail(arg2))))
    assertEquals(true, isCallAvoidableBySize(makeFunctionCall(arg1, tail(arg1))))
    assertEquals(false, isCallAvoidableBySize(makeFunctionCall(tail(arg1), tail(arg2))))
    assertEquals(true, isCallAvoidableBySize(makeFunctionCall(cons(List(nil, tail(arg1))), arg2)))
    assertEquals(false, isCallAvoidableBySize(makeFunctionCall(cons(List(nil, tail(arg1))), tail(arg2))))
    assertEquals(false, isCallAvoidableBySize(nil))
      
	}
	
	@Test
	def testHasDoubleRecursion = {
	    
    val refiner = new Refiner(prog, hole, holeFunDef)
    import refiner.hasDoubleRecursion
    
    assertEquals(2, holeFunDef.args.size)
    
    val arg1 = holeFunDef.args.head.toVariable
    val arg2 = holeFunDef.args(1).toVariable
    
    def makeFunctionCall(arg1: Expr, arg2: Expr) = FunctionInvocation(holeFunDef, Seq(arg1, arg2)) 
    
    assertEquals(false, hasDoubleRecursion(makeFunctionCall(nil, nil)))
    assertEquals(false, hasDoubleRecursion(makeFunctionCall(arg1, arg2)))
    assertEquals(false, hasDoubleRecursion(makeFunctionCall(arg2, arg1)))
    assertEquals(false, hasDoubleRecursion(makeFunctionCall(arg1, tail(arg2))))
    assertEquals(false, hasDoubleRecursion(makeFunctionCall(arg1, tail(arg1))))
    assertEquals(false, hasDoubleRecursion(makeFunctionCall(tail(arg1), tail(arg2))))
    assertEquals(false, hasDoubleRecursion(makeFunctionCall(cons(List(nil, tail(arg1))), arg2)))
    assertEquals(false, hasDoubleRecursion(makeFunctionCall(cons(List(nil, tail(arg1))), tail(arg2))))
    assertEquals(false, hasDoubleRecursion(nil))
    
    assertEquals(false, hasDoubleRecursion(And(makeFunctionCall(arg1, arg2), makeFunctionCall(arg1, arg2))))
    assertEquals(true, hasDoubleRecursion(makeFunctionCall(makeFunctionCall(arg1, arg2), tail(arg2))))
      
	}
 
	@Test
	def testIsAvoidable = {
	    
    val refiner = new Refiner(prog, hole, holeFunDef)
    import refiner.isAvoidable
    
    assertEquals(2, holeFunDef.args.size)
    
    val arg1 = holeFunDef.args.head.toVariable
    val arg2 = holeFunDef.args(1).toVariable
    
    def makeFunctionCall(arg1: Expr, arg2: Expr) = FunctionInvocation(holeFunDef, Seq(arg1, arg2)) 
    
    assertEquals(true, isAvoidable(makeFunctionCall(nil, nil)))
    assertEquals(true, isAvoidable(makeFunctionCall(arg1, arg2)))
    assertEquals(true, isAvoidable(makeFunctionCall(arg2, arg1)))
    assertEquals(false, isAvoidable(makeFunctionCall(arg1, tail(arg2))))
    assertEquals(true, isAvoidable(makeFunctionCall(arg1, tail(arg1))))
    assertEquals(false, isAvoidable(makeFunctionCall(tail(arg1), tail(arg2))))
    assertEquals(true, isAvoidable(makeFunctionCall(cons(List(nil, tail(arg1))), arg2)))
    assertEquals(false, isAvoidable(makeFunctionCall(cons(List(nil, tail(arg1))), tail(arg2))))
    assertEquals(false, isAvoidable(nil))
    
    assertEquals(true, isAvoidable(makeFunctionCall(makeFunctionCall(arg1, arg2), tail(arg2))))
      
	}
	
}