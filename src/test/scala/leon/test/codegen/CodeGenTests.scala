/* Copyright 2009-2014 EPFL, Lausanne */

package leon.test.codegen

import leon._
import leon.codegen._
import leon.purescala.Definitions._
import leon.purescala.Trees._
import leon.purescala.TypeTrees._
import leon.evaluators.{CodeGenEvaluator,EvaluationResults}
import EvaluationResults._

import java.io._

/*
 * To add a new test:
 * - Add your test, preferably in a new module, in the test variable
 * - Make sure the function under test is named "test" and has no parameters
 * - Add the test name and expected result in the result variable.
 *   Make sure the relative order of the tests matches that of code
 */
class CodeGenTests extends test.LeonTestSuite {
 
  case class TestCase(
    name : String,
    expectedResult: Expr,
    testFunction: FunDef
  )

  def runTests() = {
    val catchAll = true
  
    val pipeline = 
      utils.TemporaryInputPhase andThen
      frontends.scalac.ExtractionPhase andThen
      utils.PreprocessingPhase
    
    val ctx = createLeonContext() 
      
    val ast = pipeline.run(ctx)( (code, List()) )
    
    val testFuns = ast.definedFunctions.filter {
      _.id.name == "test"
    }.sortWith{ ( f1, f2 ) => f1.getPos < f2.getPos }
    
    val testCases = results zip testFuns map { 
      case ( (name, result), fd ) =>
        TestCase(name, result, fd)
    }

    assert(results.size == testFuns.size)
    
    for {
      requireMonitor <- Seq(false, true)
      doInstrument <- Seq(false,true)
      evaluator = new CodeGenEvaluator(createLeonContext(), ast, CodeGenParams(
        maxFunctionInvocations = if (requireMonitor) 1000 else -1, // Monitor calls and abort execution if more than X calls
        checkContracts = true,      // Generate calls that checks pre/postconditions
        doInstrument = doInstrument // Instrument reads to case classes (mainly for vanuatoo)
      ))
      TestCase(name, expected, testFunction) <- testCases
      suffix = (if (requireMonitor) "M" else "") + ( if (doInstrument) "I" else "")
    } test(name + suffix) { 
      val body = testFunction.body.get
      val params = testFunction.params map { _.id }
      val compiled = evaluator.compile(body, params).getOrElse {
        ctx.reporter.fatalError("Failed to compile test function!")
      }
      try { compiled(Nil) match {
        case Successful(res) if res == expected =>
          // Success
        case RuntimeError(_) | EvaluatorError(_) if expected.isInstanceOf[Error] => 
          // Success
        case Successful(res) => 
          ctx.reporter.fatalError(s"""
            Program $name produced wrong output.
            Output was ${res.toString}
            Expected was ${expected.toString}       
          """.stripMargin)
        case RuntimeError(mes) => 
          ctx.reporter.fatalError(s"Program $name threw runtime error with message $mes")
        case EvaluatorError(res) =>  
          ctx.reporter.fatalError(s"Evaluator failed for program $name with message $res")
      }} catch {
        // Currently, this is what we would like to catch and still succeed, but there might be more
        case _ : LeonFatalError | _ : StackOverflowError if expected.isInstanceOf[Error] =>
          // Success
        case th : Throwable => 
          if (catchAll) {
            // This is to be able to continue testing after an error
            println(s"Program $name failed!")
            th.printStackTrace()
            ctx.reporter.fatalError(s"Program $name failed\n${th.printStackTrace()}")// with message ${th.getMessage()}")
          } else { throw th }
      }
    }
  }

  val results = Seq(
    ("simple",            IntLiteral(1)),
    ("simpleBigInt",      InfiniteIntegerLiteral(1)),
    ("eager",             IntLiteral(43)),
    ("this",              IntLiteral(42) ),
    ("oldStuff",          IntLiteral(1)),
    ("methSimple",        IntLiteral(10)),
    ("methMakeBigInt",    InfiniteIntegerLiteral(42)),
    ("methSimpleBigInt",  InfiniteIntegerLiteral(10)),
    ("BigIntNoOverflow",  InfiniteIntegerLiteral(BigInt("4000000000"))),
    ("BigIntOps",         InfiniteIntegerLiteral(BigInt(7))),
    ("BigIntComp0",       BooleanLiteral(true)),
    ("BigIntComp1",       InfiniteIntegerLiteral(BigInt(17))),
    ("BigIntComp2",       InfiniteIntegerLiteral(BigInt(12))),
    ("BigIntComp3",       InfiniteIntegerLiteral(BigInt(-7))),
    ("methods",           IntLiteral(15)),
    ("lazy",              IntLiteral(1 + 5 + 1 + 6 + 2) ),
    ("modules",           IntLiteral(1 + 2 + 0) ),
    ("lazyISLazy" ,       IntLiteral(42) ),
    ("ListWithSize" ,     IntLiteral(3) ),
    ("ListWithSumMono" ,  IntLiteral(1 + 2 + 3) ),
    ("poly" ,             IntLiteral(42) ),
    ("ListHead" ,         IntLiteral(1)),
    ("ListWithSum" ,      IntLiteral(1 + 2 + 3) ), 
    // This one loops!    
    ("lazyLoops" ,        Error(Untyped, "Looping") ),
    ("Lazier" ,           IntLiteral(1 + 2 + 3) ),
    ("SetToList",         BooleanLiteral(true) )
  )



  val code = """
    
    object simple {
      abstract class Abs
      case class Conc(x : Int) extends Abs
      def test = { 
        val c = Conc(1)
        c.x
        
      }
    }
    object simple2 {
      abstract class Abs
      case class Conc(x : BigInt) extends Abs
      def test = { 
        val c = Conc(1)
        c.x
        
      }
    }
    object eager {
      abstract class Abs() {
        val foo = 42
      }
      case class Conc(x : Int) extends Abs()
      def foo = { 
        val c = Conc(1)
        c.foo + c.x
      }
      def test = foo
    }
    object thiss {
      
      case class Bar() {
        def boo = this
        def toRet = 42
      }
      
      def test = Bar().boo.toRet
    }
    object oldStuff {
      def test = 1
      case class Bar() {
        def boo = 2
      }
    }
    object methSimple {
      
      sealed abstract class Ab { 
        def f2(x : Int) = x + 5
      }
      case class Con() extends Ab { }
      
      def test = Con().f2(5)
    }
    object methSimple2 {
      
      val x: BigInt = 42

      def test = x

    }
    object methSimple3 {
      
      sealed abstract class Ab { 
        def f2(x : BigInt): BigInt = x + 5
      }
      case class Con() extends Ab { }
      
      def test = Con().f2(5)
    }
    object methSimple4 {
      
      sealed abstract class Ab { 
        def f2(x : BigInt): BigInt = x + BigInt(2000000000)
      }
      case class Con() extends Ab { }
      
      def test = Con().f2(2000000000)
    }
    object methSimple5 {
      
      def f(x: BigInt): BigInt = ((x * 2) - 10)/2
      
      def test = f(12)
    }
    object methSimple6 {
      
      def f(x: BigInt): Boolean = x == BigInt(17)
      
      def test = f(17)
    }
    object methSimple7 {
      
      def f(x: BigInt): BigInt = if(x <= 0) -x else x
      
      def test = f(-17)
    }
    object methSimple8 {
      
      def f(x: BigInt): BigInt = if(x < 0) -x else x
      
      def test = f(-12)
    }
    object methSimple9 {
      
      def f(x: BigInt): BigInt = if(x >= 0) -x else x
      
      def test = f(-7)
    }
    object methods {
      def f1 = 4 
      sealed abstract class Ab { 
        def f2(x : Int) = Cs().f3(1,2) + f1 + x + 5
      }
      case class Con() extends Ab {}
      case class Cs() {
        def f3(x : Int, y : Int) = x + y
      }
      def test = Con().f2(3) 
    }
    object lazyFields {
      def foo = 1
      sealed abstract class Ab {
        lazy val x : Int = this match {
          case Conc(t) => t + 1
          case Conc2(t) => t+2
        }
      }
      case class Conc(t : Int) extends Ab { }
      case class Conc2(t : Int) extends Ab { } 
      def test = foo + Conc(5).x + Conc2(6).x
    }
    object modules {
      def foo = 1
      val bar = 2 
      lazy val baz = 0
      def test = foo + bar + baz 
    }
    object lazyISLazy {
      abstract class Ab { lazy val x : Int = foo; def foo : Int = foo }
      case class Conc() extends Ab { }
      def test = { val willNotLoop = Conc(); 42 }
    }
    object list {
      abstract class List[T] {
         val length : Int = this match {
          case Nil() => 0
          case Cons (_, xs ) => 1 + xs.length
        }
        
      }
      case class Cons[T](hd : T, tl : List[T]) extends List[T]
      case class Nil[T]() extends List[T]      
       
      
      val l = Cons(1, Cons(2, Cons(3, Nil())))
      
      def test = l.length + Nil().length
    }
    object ListWithSumMono {
      abstract class List
      case class Cons(hd : Int, tl : List) extends List
      case class Nil() extends List     
      
      def sum (l : List) : Int = l match {
        case Nil() => 0
        case Cons(x, xs) => x + sum(xs)
      }
      
      val l = Cons(1, Cons(2, Cons(3, Nil())))
      
      def test =  sum(l)
    }
    object poly {
      case class Poly[T](poly : T) 
      def ex = Poly(42)
      def test =  ex.poly
    }
    object ListHead {
      abstract class List[T]
      case class Cons[T](hd : T, tl : List[T]) extends List[T]
      case class Nil[T]() extends List[T]      
             
      def l = Cons(1, Cons(2, Cons(3, Nil())))
      
      def test =  l.hd
    }
    object ListWithSum {
      abstract class List[T]
      case class Cons[T](hd : T, tl : List[T]) extends List[T]
      case class Nil[T]() extends List[T]      
      
      def sum (l : List[Int]) : Int = l match {
        case Nil() => 0
        case Cons(x, xs) => x + sum(xs)
      }
      
      val l = Cons(1, Cons(2, Cons(3, Nil())))
      
      def test =  sum(l)
    }
    object lazyLoops {
      abstract class Ab { lazy val x : Int = foo; def foo : Int = foo }
      case class Conc() extends Ab { }
      def test = Conc().x
    }
    object Lazier {
      import leon.lang._
      abstract class List[T] { 
        lazy val tail = this match {
          case Nil() => error[List[T]]("Nil.tail")
          case Cons(_, tl) => tl
        }
      }
      case class Cons[T](hd : T, tl : List[T]) extends List[T]
      case class Nil[T]() extends List[T]      
      
      def sum (l : List[Int]) : Int = l match {
        case Nil() => 0
        case c : Cons[Int] => c.hd + sum(c.tail)
      }
      
      val l = Cons(1, Cons(2, Cons(3, Nil())))
      
      def test =  sum(l)
    }
    object SetToList {
      import leon.collection._
      def test = {
        val s = Set(1, 2, 3, 4, 5)
        val s2 = setToList(s).content
        s == s2
      }
    }
  """

  runTests()
}
