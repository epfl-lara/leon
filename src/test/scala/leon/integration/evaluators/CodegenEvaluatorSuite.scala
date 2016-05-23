/* Copyright 2009-2016 EPFL, Lausanne */

package leon.integration.evaluators

import leon.test._
import leon.evaluators._
import leon.purescala.Definitions._
import leon.purescala.Expressions._
import leon.purescala.Types._
import leon.codegen._

class CodegenEvaluatorSuite extends LeonTestSuiteWithProgram with helpers.ExpressionsDSL{

  val sources = List("""
    import leon.lang._

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
    object bigint1 {
      
      def f(x: BigInt): BigInt = ((x * 2) - 10)/2
      
      def test = f(12)
    }
    object bigint2 {
      
      def f(x: BigInt): Boolean = x == BigInt(17)
      
      def test = f(17)
    }
    object bigint3 {
      
      def f(x: BigInt): BigInt = if(x <= 0) -x else x
      
      def test = f(-17)
    }
    object bigint4 {
      
      def f(x: BigInt): BigInt = if(x < 0) -x else x
      
      def test = f(-12)
    }
    object bigint5 {
      
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
    object ListWithSize {
      abstract class List[T] {
         val length : Int = this match {
          case Nil() => 0
          case Cons (_, xs ) => 1 + xs.length
        }
        
      }
      case class Cons[T](hd : T, tl : List[T]) extends List[T]
      case class Nil[T]() extends List[T]      
       
      
      val l = Cons(1, Cons(2, Cons(3, Nil())))
      
      def test = l.length + Nil[Int]().length
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
    object Overrides1 {
      abstract class A {
        def x = true
      }
      case class B() extends A {
        override def x = false
      }
      case class C() extends A

      def test = (B().x, C().x)
    }
    object Overrides2 {
      abstract class A {
        val x = true
      }
      case class B() extends A {
        override val x = false
      }
      case class C() extends A

      def test = (B().x, C().x)
    }
    object Arrays1 {
      def test = {
        val x = 1
        val y = 42
        val a = Array.fill(y)(x)
        a(0) + a(41)
      }
    }

    object Arrays2 {
      def test = {
        val x = 1
        val a = Array(x, x+1, x+2, x+3)
        a(0) + a(1) + a(2) + a(3)
      }
    }
  """)

  val results = Seq(
    "simple"          -> IntLiteral(1),
    "simple2"         -> InfiniteIntegerLiteral(1),
    "eager"           -> IntLiteral(43),
    "thiss"           -> IntLiteral(42) ,
    "oldStuff"        -> IntLiteral(1),
    "methSimple"      -> IntLiteral(10),
    "methSimple2"     -> InfiniteIntegerLiteral(42),
    "methSimple3"     -> InfiniteIntegerLiteral(10),
    "methSimple4"     -> InfiniteIntegerLiteral(BigInt("4000000000")),
    "bigint1"         -> InfiniteIntegerLiteral(BigInt(7)),
    "bigint2"         -> BooleanLiteral(true),
    "bigint3"         -> InfiniteIntegerLiteral(BigInt(17)),
    "bigint4"         -> InfiniteIntegerLiteral(BigInt(12)),
    "bigint5"         -> InfiniteIntegerLiteral(BigInt(-7)),
    "methods"         -> IntLiteral(15),
    "lazyFields"      -> IntLiteral(1 + 5 + 1 + 6 + 2),
    "modules"         -> IntLiteral(1 + 2 + 0),
    "lazyISLazy"      -> IntLiteral(42),
    "ListWithSize"    -> IntLiteral(3),
    "ListWithSumMono" -> IntLiteral(1 + 2 + 3),
    "poly"            -> IntLiteral(42),
    "ListHead"        -> IntLiteral(1),
    "ListWithSum"     -> IntLiteral(1 + 2 + 3),
    "lazyLoops"       -> Error(Untyped, "Looping"),// This one loops!
    "Lazier"          -> IntLiteral(1 + 2 + 3),
    "SetToList"       -> BooleanLiteral(true),
    "Overrides1"      -> Tuple(Seq(BooleanLiteral(false), BooleanLiteral(true))),
    "Overrides2"      -> Tuple(Seq(BooleanLiteral(false), BooleanLiteral(true))),
    "Arrays1"         -> IntLiteral(2),
    "Arrays2"         -> IntLiteral(10)
  )

  for {
    (name, exp) <- results
    requireMonitor <- Seq(false, true)
    doInstrument <- Seq(false,true)
  } {
    val opts = (if(requireMonitor) "monitor " else "") +
               (if(doInstrument) "instrument" else "")

    val testName = f"$name%-20s $opts%-18s"

    test("Evaluation of "+testName) { implicit fix =>
      val eval = new CodeGenEvaluator(fix._1, fix._2, params = CodeGenParams(
        maxFunctionInvocations = if (requireMonitor) 1000 else -1, // Monitor calls and abort execution if more than X calls
        checkContracts = true,      // Generate calls that checks pre/postconditions
        doInstrument = doInstrument // Instrument reads to case classes (mainly for vanuatoo)
      ))

      (eval.eval(fcall(name + ".test")()).result, exp) match {
        case (Some(res), exp) =>
          assert(res === exp)
        case (None, Error(_, _)) =>
          // OK
        case _ =>
          fail("")
      }
    }
  }
}
