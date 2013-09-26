package lesynth

import scala.util.Random

import org.junit.Assert._
import org.junit.{ Test, Ignore, Before }
import org.scalatest.junit.JUnitSuite

import insynth.leon.loader.LeonLoader
import insynth.leon._

import _root_.leon.purescala.Trees._
import _root_.leon.purescala.TypeTrees._
import _root_.leon.purescala._
import _root_.leon.purescala.Definitions._

import lesynth.refinement._

import _root_.util._

class FilterTest extends JUnitSuite {

  import TreeOps._
  import Scaffold._
  
	val lesynthTestDir = "testcases/condabd/test/lesynth/"

  val rnd = new Random(System.currentTimeMillis())
  
  var filter: Filter = _
  
  var prog: Program = _
  var funDef: FunDef = _
  var variableRefiner: VariableRefiner = _
  
  var tail: UnaryReconstructionExpression = _
  var head: UnaryReconstructionExpression = _
  var nil: Expr = _
  var cons: NaryReconstructionExpression = _
  
  @Before
  def extract = {
    
    val problems = forFile(lesynthTestDir + "/ListConcat.scala")
		assertEquals(1, problems.size)		
    
		val (sctx, funDef, problem) = problems.head		
		
		prog = sctx.program
    this.funDef = funDef
	
    val loader = new LeonLoader(prog, problem.as, true)
    
    variableRefiner = new VariableRefiner(loader.directSubclassesMap, loader.variableDeclarations,
  		loader.classMap, sctx.reporter)
    
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
  
    filter = new Filter(prog, funDef, variableRefiner)
  }
	  
	@Test
	def testIsLess = {
	  val filter = this.filter
	    import filter.isLess
	    
	    assertEquals(2, funDef.args.size)
	    
	    val variable1 = funDef.args.head
	    val variable2 = funDef.args(1)
	    
	    assertEquals(+1, isLess(cons(List(UnitLiteral, variable1.toVariable)), variable1.id))
	    assertEquals(+1, isLess(cons(List(UnitLiteral, variable1.toVariable)), variable2.id))
	    assertEquals(-1, isLess(tail(variable1.toVariable), variable1.id))
	    assertEquals(+1, isLess(head(variable1.toVariable), variable1.id))
	    assertEquals(0, isLess(variable1.toVariable, variable1.id))
	    assertEquals(1, isLess(variable1.toVariable, variable2.id))
	    assertEquals(1, isLess(tail(variable1.toVariable), variable2.id))
	    assertEquals(1, isLess(head(variable1.toVariable), variable2.id))
	    assertEquals(1, isLess(nil, variable2.id))
        
	}
  
	@Test
	def testIsCallLessBySize = {
	    
	  val filter = this.filter
    import filter.isCallAvoidableBySize
    
    assertEquals(2, funDef.args.size)
    
    val arg1 = funDef.args.head.toVariable
    val arg2 = funDef.args(1).toVariable
    
    def makeFunctionCall(arg1: Expr, arg2: Expr) = FunctionInvocation(funDef, Seq(arg1, arg2)) 
    
    val arguments = funDef.args.map(_.id).toList
    
    assertEquals(true, isCallAvoidableBySize(makeFunctionCall(nil, nil), arguments))
    assertEquals(true, isCallAvoidableBySize(makeFunctionCall(arg1, arg2), arguments))
    assertEquals(true, isCallAvoidableBySize(makeFunctionCall(arg2, arg1), arguments))
    assertEquals(false, isCallAvoidableBySize(makeFunctionCall(arg1, tail(arg2)), arguments))
    assertEquals(true, isCallAvoidableBySize(makeFunctionCall(arg1, tail(arg1)), arguments))
    assertEquals(false, isCallAvoidableBySize(makeFunctionCall(tail(arg1), tail(arg2)), arguments))
    assertEquals(true, isCallAvoidableBySize(makeFunctionCall(cons(List(nil, tail(arg1))), arg2), arguments))
    assertEquals(false, isCallAvoidableBySize(makeFunctionCall(cons(List(nil, tail(arg1))), tail(arg2)), arguments))
    assertEquals(false, isCallAvoidableBySize(nil, arguments))
      
	}
	
	@Test
	def testHasDoubleRecursion = {
	    
	  val filter = this.filter
    import filter.hasDoubleRecursion
    
    assertEquals(2, funDef.args.size)
    
    val arg1 = funDef.args.head.toVariable
    val arg2 = funDef.args(1).toVariable
    
    def makeFunctionCall(arg1: Expr, arg2: Expr) = FunctionInvocation(funDef, Seq(arg1, arg2)) 
    
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
	    
    val filter = this.filter
    import filter.isAvoidable
    
    assertEquals(2, funDef.args.size)
    
    val arg1 = funDef.args.head.toVariable
    val arg2 = funDef.args(1).toVariable
    
    def makeFunctionCall(arg1: Expr, arg2: Expr) = FunctionInvocation(funDef, Seq(arg1, arg2))  
    
    val arguments = funDef.args.map(_.id).toList
    
    assertEquals(true, isAvoidable(makeFunctionCall(nil, nil), arguments))
    assertEquals(true, isAvoidable(makeFunctionCall(arg1, arg2), arguments))
    assertEquals(true, isAvoidable(makeFunctionCall(arg2, arg1), arguments))
    assertEquals(false, isAvoidable(makeFunctionCall(arg1, tail(arg2)), arguments))
    assertEquals(true, isAvoidable(makeFunctionCall(arg1, tail(arg1)), arguments))
    assertEquals(false, isAvoidable(makeFunctionCall(tail(arg1), tail(arg2)), arguments))
    assertEquals(true, isAvoidable(makeFunctionCall(cons(List(nil, tail(arg1))), arg2), arguments))
    assertEquals(false, isAvoidable(makeFunctionCall(cons(List(nil, tail(arg1))), tail(arg2)), arguments))
    assertEquals(false, isAvoidable(nil, arguments))
    
    assertEquals(true, isAvoidable(makeFunctionCall(makeFunctionCall(arg1, arg2), tail(arg2)), arguments))
      
	}
	
	@Test
	def testIsAvoidableUneccessaryStructure {
	    
    val filter = this.filter
    import filter.isAvoidable
    
    val arg1 = funDef.args.head.toVariable
    val arg2 = funDef.args(1).toVariable
    val arguments = funDef.args.map(_.id).toList
    
    val tpe = cons(List(Error("temp"))).getType match {
      case cct: CaseClassType => cct.classDef
      case _ =>
        fail(arg1 + " should have a class type")
        null
    }    
    
    assertEquals(false, isAvoidable(CaseClassInstanceOf(tpe, arg1), arguments))
	  assertEquals(false, isAvoidable(CaseClassInstanceOf(tpe, arg2), arguments))
	  assertEquals(false, isAvoidable(CaseClassInstanceOf(tpe, cons(List(arg1, nil))), arguments))
	  assertEquals(true, isAvoidable(CaseClassInstanceOf(tpe, tail(arg1)), arguments))
	  assertEquals(true, isAvoidable(CaseClassInstanceOf(tpe, tail(tail(arg1))), arguments))
	  assertEquals(true, isAvoidable(CaseClassInstanceOf(tpe, tail(tail(tail(tail(arg1))))), arguments))
	}
	
}