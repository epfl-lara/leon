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

case class TestCase(
  name : String, 
  content : String,  
  expected : Expr,
  args : Seq[Expr] = Seq(),
  functionToTest : String = "test"
)

class CodeGenTests extends test.LeonTestSuite {
  
  val catchAll = true
  
  val pipeline = 
    utils.TemporaryInputPhase andThen
    frontends.scalac.ExtractionPhase andThen
    utils.PreprocessingPhase

  def compileTestFun(p : Program, toTest : String, ctx : LeonContext, requireMonitor : Boolean, doInstrument : Boolean) : ( Seq[Expr] => EvaluationResults.Result) = {
    // We want to produce code that checks contracts
    val evaluator = new CodeGenEvaluator(ctx, p, CodeGenParams(
      maxFunctionInvocations = if (requireMonitor) 1000 else -1, // Monitor calls and abort execution if more than X calls
      checkContracts = true,      // Generate calls that checks pre/postconditions
      doInstrument = doInstrument // Instrument reads to case classes (mainly for vanuatoo)
    ))
   

    val testFun =  p.definedFunctions.find(_.id.name == toTest).getOrElse {
      ctx.reporter.fatalError("Test function not defined!")
    }
    val params = testFun.params map { _.id }
    val body = testFun.body.get
    // Will apply test a number of times with the help of compileRec
    evaluator.compile(body, params).getOrElse {
      ctx.reporter.fatalError("Failed to compile test function!")
    }
       
  }
 
  
  private def testCodeGen(prog : TestCase, requireMonitor : Boolean, doInstrument : Boolean) { test(prog.name) {
    import prog._
    val ctx = testContext.copy(
      // We want a reporter that actually prints some output
      reporter = new DefaultReporter(testContext.settings)
    )
    
    val ast = pipeline.run(ctx)( (content, List()) )
    
    //ctx.reporter.info(purescala.ScalaPrinter(ast))
    
    val compiled = compileTestFun(ast, functionToTest, ctx, requireMonitor, doInstrument)
    try { compiled(args) match {
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
          ctx.reporter.fatalError(s"Program $name failed\n${th.printStackTrace()}")// with message ${th.getMessage()}")
        } else { throw th }
    }
  }}
  

  val programs = Seq(
    
    TestCase("simple", """
      object simple {
        abstract class Abs
        case class Conc(x : Int) extends Abs
        def test = { 
          val c = Conc(1)
          c.x
          
        }
      }""",
      IntLiteral(1)
    ),  
      
    TestCase("eager", """
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
      }""",
      IntLiteral(43)
    ),
    
    TestCase("this", """ 
      object thiss {
        
        case class Bar() {
          def boo = this
          def toRet = 42
        }
        
        def test = Bar().boo.toRet
      }
      """,
      IntLiteral(42)
    ),
    
   TestCase("oldStuff", """ 
      object oldStuff {
        def test = 1
        case class Bar() {
          def boo = 2
        }
      }""",
      IntLiteral(1)
    ),
    
    TestCase("methSimple", """
      object methSimple {
        
        sealed abstract class Ab { 
          def f2(x : Int) = x + 5
        }
        case class Con() extends Ab { }
        
        def test = Con().f2(5)
      }""",
      IntLiteral(10)
    ),
    
    TestCase("methods", """
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
      }""",
      IntLiteral(15)
    ),
    
    
    TestCase("lazy", """
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
      """, 
      IntLiteral(1 + 5 + 1 + 6 + 2)
    ),
    
    TestCase("modules", """
      object modules {
        def foo = 1
        val bar = 2 
        lazy val baz = 0
        def test = foo + bar + baz 
      }
      """, 
      IntLiteral(1 + 2 + 0)
    ),
    
    TestCase("lazyISLazy" , """ 
      object lazyISLazy {
        abstract class Ab { lazy val x : Int = foo; def foo : Int = foo }
        case class Conc() extends Ab { }
        def test = { val willNotLoop = Conc(); 42 }
      }""",
      IntLiteral(42)
    ),
    
    TestCase("ListWithSize" , """ 
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
      }""",
      IntLiteral(3 )
    ),
    
    TestCase("ListWithSumMono" , """ 
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
      }""",
      IntLiteral(1 + 2 + 3)
    ),
    
    TestCase("poly" , """ 
      object poly {
        case class Poly[T](poly : T) 
        def ex = Poly(42)
        def test =  ex.poly
      }""",
      IntLiteral(42)
    ),
    
    TestCase("ListHead" , """ 
      object ListHead {
        abstract class List[T]
        case class Cons[T](hd : T, tl : List[T]) extends List[T]
        case class Nil[T]() extends List[T]      
               
        def l = Cons(1, Cons(2, Cons(3, Nil())))
        
        def test =  l.hd
      }""",
      IntLiteral(1)
    ),
    TestCase("ListWithSum" , """ 
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
      }""",
      IntLiteral(1 + 2 + 3)
    ), 
     
    // This one loops!    
    TestCase("lazyLoops" , """ 
        object lazyLoops {
          abstract class Ab { lazy val x : Int = foo; def foo : Int = foo }
          case class Conc() extends Ab { }
          def test = Conc().x
        }""",
        Error(Untyped, "Looping")
    ),
    
    TestCase("Lazier" , """
      import leon.lang._
      object Lazier {
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
      }""",
      IntLiteral(1 + 2 + 3)
    )
  )
  
  
  
  for ( prog <- programs ;
        requireMonitor <- Seq(false ,true );
        doInstrument <- Seq(false,true )
        
      ) {
    testCodeGen(
      prog.copy(name = prog.name + (if (requireMonitor)"_M_" else "" ) + (if (doInstrument)"_I_" else "" )), 
      requireMonitor, doInstrument
    )}
}
