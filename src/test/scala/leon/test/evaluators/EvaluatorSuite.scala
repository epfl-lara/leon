/* Copyright 2009-2015 EPFL, Lausanne */

package leon.test.allEvaluators

import leon._
import leon.test._
import leon.evaluators._

import leon.utils.{TemporaryInputPhase, PreprocessingPhase}
import leon.frontends.scalac.ExtractionPhase

import leon.purescala.Common._
import leon.purescala.Definitions._
import leon.purescala.Expressions._
import leon.purescala.DefOps._
import leon.purescala.Types._
import leon.purescala.Extractors._
import leon.purescala.Constructors._
import leon.codegen._

class EvaluatorSuite extends LeonTestSuiteWithProgram with helpers.ExpressionsDSL {

  val sources = List(
    """|object Arithmetic {
       |  def plus(x : Int, y : Int) : Int = x + y
       |  def max(x : Int, y : Int) : Int = if(x >= y) x else y
       |  def square(i : Int) : Int = { val j = i; j * i }
       |  def abs(i : Int) : Int = if(i < 0) -i else i
       |  def intSqrt(n : Int) : Int = intSqrt0(abs(n), 0)
       |  def intSqrt0(n : Int, c : Int) : Int = {
       |    val s = square(c+1)
       |    if(s > n) c else intSqrt0(n, c+1)
       |  }
       |  def div(x : Int, y : Int) : Int = (x / y)
       |  def rem(x : Int, y : Int) : Int = (x % y)
       |}
       |""".stripMargin,

    """|object BigIntArithmetic {
       |  def plus(x : BigInt, y : BigInt) : BigInt = x + y
       |  def max(x : BigInt, y : BigInt) : BigInt = if(x >= y) x else y
       |  def square(i : BigInt) : BigInt = { val j = i; j * i }
       |  def abs(i : BigInt) : BigInt = if(i < 0) -i else i
       |  def intSqrt(n : BigInt) : BigInt = intSqrt0(abs(n), 0)
       |  def intSqrt0(n : BigInt, c : BigInt) : BigInt = {
       |    val s = square(c+1)
       |    if(s > n) c else intSqrt0(n, c+1)
       |  }
       |  def div(x : BigInt, y : BigInt) : BigInt = (x / y)
       |  def rem(x : BigInt, y : BigInt) : BigInt = (x % y)
       |  def mod(x : BigInt, y : BigInt) : BigInt = (x mod y)
       |}
       |""".stripMargin,

    """|import leon.lang._
       |object RealArithmetic {
       |  def plus(x : Real, y : Real) : Real = x + y
       |  def max(x : Real, y : Real) : Real = if(x >= y) x else y
       |  def square(i : Real) : Real = { val j = i; j * i }
       |  def abs(i : Real) : Real = if(i < Real(0)) -i else i
       |  def intSqrt(n : Real) : Real = intSqrt0(abs(n), Real(0))
       |  def intSqrt0(n : Real, c : Real) : Real = {
       |    val s = square(c+Real(1))
       |    if(s > n) c else intSqrt0(n, c+Real(1))
       |  }
       |  def div(x : Real, y : Real) : Real = (x / y)
       |}
       |""".stripMargin,

    """|object Booleans {
       |  def and1(x : Boolean, y : Boolean) : Boolean = x && y
       |  def or1(x : Boolean, y : Boolean)  : Boolean = x || y
       |  def and2(x : Boolean, y : Boolean) : Boolean = !(!x || !y)
       |  def or2(x : Boolean, y : Boolean)  : Boolean = !(!x && !y)
       |  def safe(n : Int) : Boolean = (n != 0 && (1/n == n))
       |  def mkTrue() : Boolean = true
       |  def mkFalse() : Boolean = false
       |}""".stripMargin,

    """|object CaseClasses {
       |  sealed abstract class List
       |  case class Nil() extends List
       |  case class Cons(head : Int, tail : List) extends List
       |
       |  case class MySingleton(i : Int)
       |
       |  def size(l : List) : Int = l match {
       |    case Nil() => 0
       |    case Cons(_, xs) => 1 + size(xs)
       |  }
       |
       |  def compare(l1 : List, l2 : List) : Boolean = (l1 == l2)
       |
       |  def head(l : List) : Int = l match {
       |    case Cons(h, _) => h
       |  }
       |
       |  def wrap(i : Int) : MySingleton = MySingleton(i)
       |}""".stripMargin,

    """|import leon.lang._
       |object Sets {
       |  sealed abstract class List
       |  case class Nil() extends List
       |  case class Cons(head : Int, tail : List) extends List
       |
       |  def content(l : List) : Set[Int] = l match {
       |    case Nil() => Set.empty[Int]
       |    case Cons(x, xs) => Set(x) ++ content(xs)
       |  }
       |
       |  def finite() : Set[Int] = Set(1, 2, 3)
       |  def build(x : Int, y : Int, z : Int) : Set[Int] = Set(x, y, z)
       |  def union(s1 : Set[Int], s2 : Set[Int]) : Set[Int] = s1 ++ s2
       |  def inter(s1 : Set[Int], s2 : Set[Int]) : Set[Int] = s1 & s2
       |  def diff(s1 : Set[Int], s2 : Set[Int]) : Set[Int] = s1 -- s2
       |}""".stripMargin,

    """|import leon.lang._
       |object Maps {
       |  sealed abstract class PList
       |  case class PNil() extends PList
       |  case class PCons(headfst : Int, headsnd : Int, tail : PList) extends PList
       |
       |  def toMap(pl : PList) : Map[Int,Int] = pl match {
       |    case PNil() => Map.empty[Int,Int]
       |    case PCons(f,s,xs) => toMap(xs).updated(f, s)
       |  }
       |
       |  def finite0() : Map[Int,Int] = Map[Int, Int]()
       |  def finite1() : Map[Int,Int] = Map(1 -> 2)
       |  def finite2() : Map[Int,Int] = Map(2 -> 3, 1 -> 2)
       |  def finite3() : Map[Int,Int] = finite1().updated(2, 3)
       |}""".stripMargin,

    """|import leon.lang._
       |object Arrays {
       |  def boolArrayRead(bools : Array[Boolean], index : Int) : Boolean = bools(index)
       |
       |  def intArrayRead(ints : Array[Int], index : Int) : Int = ints(index)
       |
       |  def intArrayUpdate(ints : Array[Int], index : Int, value: Int) : Int = {
       |    val na = ints.updated(index, value)
       |    na(index)
       |  }
       |}
       |""".stripMargin,

    """|import leon.lang._
       |object Sets2 {
       |  case class MyPair(x : Int, y : Boolean)
       |
       |  def buildPairCC(x : Int, y : Boolean) : MyPair = MyPair(x,y)
       |  def mkSingletonCC(p : MyPair) : Set[MyPair] = Set(p)
       |  def containsCC(s : Set[MyPair], p : MyPair) : Boolean = s.contains(p)
       |
       |  def buildPairT(x : Int, y : Boolean) : (Int,Boolean) = (x,y)
       |  def mkSingletonT(p : (Int,Boolean)) : Set[(Int,Boolean)] = Set(p)
       |  def containsT(s : Set[(Int,Boolean)], p : (Int,Boolean)) : Boolean = s.contains(p)
       |}""".stripMargin,

    """|import leon.lang._
       |import leon.lang.synthesis._
       |object Choose {
       |  def c(i : Int) : Int = choose { (j : Int) => j > i && j < i + 2 }
       |}
       |""".stripMargin,

    """|import leon.lang._
       |object Recursion {
       |  import leon.lang._
       |
       |  def c(i : Int) : Int = c(i-1)
       |}
       |""".stripMargin,

    """|import leon.lang._
       |object Contracts {
       |
       |  def c(i : Int) : Int = {
       |    require(i > 0);
       |    c(i-1)
       |  }
       |}
       |""".stripMargin,

    """|import leon.lang._
       |object PatMat {
       |  abstract class List;
       |  case class Cons(h: Int, t: List) extends List;
       |  case object Nil extends List;
       |
       |  def f1: Int = (Cons(1, Nil): List) match {
       |    case Cons(h, t) => h
       |    case Nil => 0
       |  }
       |
       |  def f2: Int = (Cons(1, Nil): List) match {
       |    case Cons(h, _) => h
       |    case Nil => 0
       |  }
       |
       |  def f3: Int = (Nil: List) match {
       |    case _ => 1
       |  }
       |
       |  def f4: Int = (Cons(1, Cons(2, Nil)): List) match {
       |    case a: Cons => 1
       |    case _ => 0
       |  }
       |
       |  def f5: Int = ((Cons(1, Nil), Nil): (List, List)) match {
       |    case (a: Cons, _) => 1
       |    case _ => 0
       |  }
       |
       |  def f6: Int = (Cons(2, Nil): List) match {
       |    case Cons(h, t) if h > 0 => 1
       |    case _ => 0
       |  }
       |}""".stripMargin,

    """import leon.lang._
      |object Lambda {
      |  val foo1 = (x: BigInt) => x
      |  val foo2 = {
      |    val a = BigInt(1)
      |    (x: BigInt) => a + x
      |  }
      |  val foo3 = {
      |    val f1 = (x: BigInt) => x + 1
      |    val f2 = (x: BigInt) => x + 2
      |    (x: BigInt, y: BigInt) => f1(x) + f2(y)
      |  }
      |  def foo4(x: BigInt) = (i: BigInt) => i + x
      |}""".stripMargin,

    """object Methods {
      |  abstract class A
      |
      |  abstract class B extends A {
      |    def foo(i: BigInt) = {
      |      require(i > 0)
      |      i + 1
      |    } ensuring ( _ >= 0 )
      |  }
      |
      |  case class C(x: BigInt) extends B {
      |    val y = BigInt(42)
      |    override def foo(i: BigInt) = {
      |      x + y + (if (i>0) i else -i)
      |    } ensuring ( _ >= x )
      |  }
      |
      |  case class D() extends A
      |
      |  def f1 = {
      |    val c = C(42)
      |    (if (c.foo(0) + c.x > 0) c else D()).isInstanceOf[B]
      |  }
      |  def f2 = D().isInstanceOf[B]
      |  def f3 = C(42).isInstanceOf[A]
      |}""".stripMargin
  )

  def normalEvaluators(implicit ctx: LeonContext, pgm: Program): List[Evaluator] = {
    List(
      new DefaultEvaluator(ctx, pgm)
    )
  }

  def codegenEvaluators(implicit ctx: LeonContext, pgm: Program): List[Evaluator] = {
    List(
      new CodeGenEvaluator(ctx, pgm)
    )
  }

  def allEvaluators(implicit ctx: LeonContext, pgm: Program): List[Evaluator] = {
    normalEvaluators ++ codegenEvaluators
  }

  test("Arithmetic") { implicit fix =>
    for(e <- allEvaluators) {
      // Some simple math.
      eval(e, fcall("Arithmetic.plus")(i(60), BVUMinus(i(18))))   === i(42)
      eval(e, fcall("Arithmetic.max")(i(4), i(42)))               === i(42)
      eval(e, fcall("Arithmetic.max")(i(42), BVUMinus(i(42))))    === i(42)
      eval(e, fcall("Arithmetic.intSqrt")(BVUMinus(i(1800))))      === i(42)
      eval(e, fcall("Arithmetic.div")(i(7), i(5)))                === i(1)
      eval(e, fcall("Arithmetic.div")(i(7), i(-5)))               === i(-1)
      eval(e, fcall("Arithmetic.div")(i(-7), i(5)))               === i(-1)
      eval(e, fcall("Arithmetic.div")(i(-7), i(-5)))              === i(1)
      eval(e, fcall("Arithmetic.rem")(i(7), i(5)))                === i(2)
      eval(e, fcall("Arithmetic.rem")(i(7), i(-5)))               === i(2)
      eval(e, fcall("Arithmetic.rem")(i(-7), i(5)))               === i(-2)
      eval(e, fcall("Arithmetic.rem")(i(-7), i(-5)))              === i(-2)
      eval(e, fcall("Arithmetic.rem")(i(-1), i(5)))               === i(-1)

      // Things that should crash.
      eval(e, fcall("Arithmetic.div")(i(42), i(0))).failed
      eval(e, fcall("Arithmetic.rem")(i(42), i(0))).failed
    }
  }

  test("BigInt Arithmetic") { implicit fix =>
    for(e <- allEvaluators) {
      // Some simple math.
      eval(e, fcall("BigIntArithmetic.plus")(bi(60), UMinus(bi(18))))    === bi(42)
      eval(e, fcall("BigIntArithmetic.max")(bi(4), bi(42)))              === bi(42)
      eval(e, fcall("BigIntArithmetic.max")(bi(42), UMinus(bi(42))))     === bi(42)
      eval(e, fcall("BigIntArithmetic.intSqrt")(UMinus(bi(1800))))        === bi(42)
      eval(e, fcall("BigIntArithmetic.div")(bi(7), bi(5)))               === bi(1)
      eval(e, fcall("BigIntArithmetic.div")(bi(7), bi(-5)))              === bi(-1)
      eval(e, fcall("BigIntArithmetic.div")(bi(-7), bi(5)))              === bi(-1)
      eval(e, fcall("BigIntArithmetic.div")(bi(-7), bi(-5)))             === bi(1)
      eval(e, fcall("BigIntArithmetic.rem")(bi(7), bi(5)))               === bi(2)
      eval(e, fcall("BigIntArithmetic.rem")(bi(7), bi(-5)))              === bi(2)
      eval(e, fcall("BigIntArithmetic.rem")(bi(-7), bi(5)))              === bi(-2)
      eval(e, fcall("BigIntArithmetic.rem")(bi(-7), bi(-5)))             === bi(-2)
      eval(e, fcall("BigIntArithmetic.rem")(bi(-1), bi(5)))              === bi(-1)
      eval(e, fcall("BigIntArithmetic.mod")(bi(7), bi(5)))               === bi(2)
      eval(e, fcall("BigIntArithmetic.mod")(bi(7), bi(-5)))              === bi(2)
      eval(e, fcall("BigIntArithmetic.mod")(bi(-7), bi(5)))              === bi(3)
      eval(e, fcall("BigIntArithmetic.mod")(bi(-7), bi(-5)))             === bi(3)
      eval(e, fcall("BigIntArithmetic.mod")(bi(-1), bi(5)))              === bi(4)

      // Things that should crash.
      eval(e, fcall("BigIntArithmetic.div")(bi(42), bi(0))).failed 
      eval(e, fcall("BigIntArithmetic.rem")(bi(42), bi(0))).failed
      eval(e, fcall("BigIntArithmetic.mod")(bi(42), bi(0))).failed
    }
  }

  test("Real Arithmetic") { implicit fix =>
    for(e <- allEvaluators) {
      // Some simple math.
      eval(e, fcall("RealArithmetic.plus")(r(60), RealUMinus(r(18))))    === r(42)
      eval(e, fcall("RealArithmetic.max")(r(4), r(42)))                  === r(42)
      eval(e, fcall("RealArithmetic.max")(r(42), RealUMinus(r(42))))     === r(42)
      eval(e, fcall("RealArithmetic.intSqrt")(RealUMinus(r(1800))))      === r(42)
      eval(e, fcall("RealArithmetic.div")(r(7), r(7)))                   === r(1)
      eval(e, fcall("RealArithmetic.div")(r(5), r(2)))                   === r(2.5)

      // Things that should crash.
      eval(e, fcall("RealArithmetic.div")(r(42), r(0))).failed
    }
  }

  test("Booleans") { implicit fix =>
    for(e <- allEvaluators) {
      eval(e, fcall("Booleans.and1")(F, F)) === F
      eval(e, fcall("Booleans.and1")(F, T)) === F
      eval(e, fcall("Booleans.and1")(T, F)) === F
      eval(e, fcall("Booleans.and1")(T, T)) === T
      eval(e, fcall("Booleans.and2")(F, F)) === F
      eval(e, fcall("Booleans.and2")(F, T)) === F
      eval(e, fcall("Booleans.and2")(T, F)) === F
      eval(e, fcall("Booleans.and2")(T, T)) === T
      eval(e, fcall("Booleans.or1")(F, F))  === F
      eval(e, fcall("Booleans.or1")(F, T))  === T
      eval(e, fcall("Booleans.or1")(T, F))  === T
      eval(e, fcall("Booleans.or1")(T, T))  === T
      eval(e, fcall("Booleans.or2")(F, F))  === F
      eval(e, fcall("Booleans.or2")(F, T))  === T
      eval(e, fcall("Booleans.or2")(T, F))  === T
      eval(e, fcall("Booleans.or2")(T, T))  === T

      eval(e, fcall("Booleans.safe")(i(1))) === T
      eval(e, fcall("Booleans.safe")(i(2))) === F

      // This one needs short-circuit.
      eval(e, fcall("Booleans.safe")(i(0))) === F

      // We use mkTrue/mkFalse to avoid automatic simplifications.
      eval(e, Equals(fcall("Booleans.mkTrue")(),  fcall("Booleans.mkTrue")()))  === T
      eval(e, Equals(fcall("Booleans.mkTrue")(),  fcall("Booleans.mkFalse")())) === F
      eval(e, Equals(fcall("Booleans.mkFalse")(), fcall("Booleans.mkTrue")()))  === F
      eval(e, Equals(fcall("Booleans.mkFalse")(), fcall("Booleans.mkFalse")())) === T

      eval(e, Implies(fcall("Booleans.mkTrue")(),  fcall("Booleans.mkTrue")()))  === T
      eval(e, Implies(fcall("Booleans.mkTrue")(),  fcall("Booleans.mkFalse")())) === F
      eval(e, Implies(fcall("Booleans.mkFalse")(), fcall("Booleans.mkTrue")()))  === T
      eval(e, Implies(fcall("Booleans.mkFalse")(), fcall("Booleans.mkFalse")())) === T
    }
  }

  test("Case classes") { implicit fix =>
    val nil = cc("CaseClasses.Nil")()
    def cons(es: Expr*) = cc("CaseClasses.Cons")(es: _*)

    val cons12a = cons(i(1), cons(i(2), nil))
    val cons12b = cons(i(1), cons(i(2), nil))
    val sing1   = cc("CaseClasses.MySingleton")(i(1))

    for(e <- allEvaluators) {
      eval(e, fcall("CaseClasses.size")(nil))                  === i(0)
      eval(e, fcall("CaseClasses.size")(cons12a))              === i(2)
      eval(e, fcall("CaseClasses.compare")(nil, cons12a))      === F
      eval(e, fcall("CaseClasses.compare")(cons12a, cons12b))  === T
      eval(e, fcall("CaseClasses.head")(cons12a))              === i(1)

      eval(e, Equals(fcall("CaseClasses.wrap")(i(1)), sing1)) === T

      // Match error
      eval(e, fcall("CaseClasses.head")(nil)).failed
    }
  }

  test("Sets") { implicit fix  =>
    val nil = cc("Sets.Nil")()
    def cons(es: Expr*) = cc("Sets.Cons")(es: _*)

    val cons12 = cons(i(1), cons(i(2), nil))

    val es     = FiniteSet(Set(), Int32Type)
    val s2     = FiniteSet(Set(i(2)), Int32Type)
    val s12    = FiniteSet(Set(i(1), i(2)), Int32Type)
    val s13    = FiniteSet(Set(i(1), i(3)), Int32Type)
    val s46    = FiniteSet(Set(i(4), i(6)), Int32Type)
    val s123   = FiniteSet(Set(i(1), i(2), i(3)), Int32Type)
    val s246   = FiniteSet(Set(i(2), i(4), i(6)), Int32Type)
    val s12346 = FiniteSet(Set(i(1), i(2), i(3), i(4), i(6)), Int32Type)

    for(e <- allEvaluators) {
      eval(e, fcall("Sets.finite")())                === s123
      eval(e, fcall("Sets.content")(nil))            === es
      eval(e, fcall("Sets.content")(cons12))         === s12
      eval(e, fcall("Sets.build")(i(1), i(2), i(3))) === s123
      eval(e, fcall("Sets.build")(i(1), i(2), i(2))) === s12
      eval(e, fcall("Sets.union")(s123, s246))       === s12346
      eval(e, fcall("Sets.union")(s246, s123))       === s12346
      eval(e, fcall("Sets.inter")(s123, s246))       === s2
      eval(e, fcall("Sets.inter")(s246, s123))       === s2
      eval(e, fcall("Sets.diff")(s123, s246))        === s13
      eval(e, fcall("Sets.diff")(s246, s123))        === s46

      eval(e, Equals(fcall("Sets.union")(s123, s246), fcall("Sets.union")(s246, s123))) === T
      eval(e, Equals(fcall("Sets.inter")(s123, s246), fcall("Sets.inter")(s246, s123))) === T
      eval(e, Equals(fcall("Sets.diff")(s123, s246), fcall("Sets.diff")(s246, s123)))   === F
    }
  }

  test("Maps") { implicit fix  =>
    val cons1223 = cc("Maps.PCons")(i(1), i(2), cc("Maps.PCons")(i(2), i(3), cc("Maps.PNil")()))

    def eqMap(a: Expr, m: Map[Expr, Expr]) = a match {
      case FiniteMap(es1, _, _) =>
        es1.toMap === m
      case e =>
        fail("Expected FiniteMap, got "+e)
    }

    val em     = FiniteMap(Seq(), Int32Type, Int32Type)

    for(e <- allEvaluators) {
      eqMap(eval(e, fcall("Maps.finite0")()).res, Map())
      eqMap(eval(e, fcall("Maps.finite1")()).res, Map(i(1) -> i(2)))
      eqMap(eval(e, fcall("Maps.finite2")()).res, Map(i(1) -> i(2), i(2) -> i(3)))
      eqMap(eval(e, fcall("Maps.toMap")(cons1223)).res, Map(i(1) -> i(2), i(2) -> i(3)))

      eval(e, Equals(fcall("Maps.finite1")(), fcall("Maps.finite2")())) === F
      eval(e, Equals(fcall("Maps.finite2")(), fcall("Maps.finite3")())) === T
      eval(e, MapIsDefinedAt(fcall("Maps.finite2")(), i(2)))          === T
      eval(e, MapIsDefinedAt(fcall("Maps.finite2")(), i(3)))          === F
    }
  }

  test("Arrays") { implicit fix =>
    val ba = finiteArray(Seq(T, F))
    val ia = finiteArray(Seq(i(41), i(42), i(43)))

    for(e <- allEvaluators) {
      eval(e, fcall("Arrays.boolArrayRead")(ba, i(0))) === T
      eval(e, fcall("Arrays.boolArrayRead")(ba, i(1))) === F
      eval(e, fcall("Arrays.intArrayRead")(ia, i(0)))  === i(41)
      eval(e, fcall("Arrays.intArrayRead")(ia, i(1)))  === i(42)

      eval(e, ArrayLength(ia)) === i(3)

      eval(e, fcall("Arrays.intArrayUpdate")(ia, i(0), i(13))) === i(13)
      eval(e, fcall("Arrays.intArrayUpdate")(ia, i(1), i(17))) === i(17)

      eval(e, fcall("Arrays.boolArrayRead")(ba, i(2))).failed
    }
  }

  test("Sets and maps of structures") { implicit fix =>
    for(e <- allEvaluators) {
      eval(e, fcall("Sets2.containsCC")(fcall("Sets2.mkSingletonCC")(fcall("Sets2.buildPairCC")(i(42), T)), fcall("Sets2.buildPairCC")(i(42), T))) === T
      eval(e, fcall("Sets2.containsT")(fcall("Sets2.mkSingletonT")(fcall("Sets2.buildPairT")(i(42), T)), fcall("Sets2.buildPairT")(i(42), T))) === T
    }
  }

  test("Executing Chooses") { implicit fix =>
    for(e <- allEvaluators) {
      eval(e, fcall("Choose.c")(i(42))) === i(43)
    }
  }

  test("Infinite Recursion") { implicit fix =>
    val e = new CodeGenEvaluator(fix._1, fix._2, CodeGenParams.default.copy(maxFunctionInvocations = 32))

    eval(e, fcall("Recursion.c")(i(42))).failed
  }

  test("Wrong Contracts") { implicit fix =>
    for(e <- allEvaluators) {
      eval(e, fcall("Contracts.c")(i(-42))).failed
    }
  }

  test("Pattern Matching") { implicit fix =>
    for(e <- allEvaluators) {
      // Some simple math.
      eval(e, fcall("PatMat.f1")()) === i(1)
      eval(e, fcall("PatMat.f2")()) === i(1)
      eval(e, fcall("PatMat.f3")()) === i(1)
      eval(e, fcall("PatMat.f4")()) === i(1)
      eval(e, fcall("PatMat.f5")()) === i(1)
      eval(e, fcall("PatMat.f6")()) === i(1)
    }
  }

  test("Lambda functions") { implicit fix =>
    def checkLambda(evaluator: Evaluator, in: Expr, out: PartialFunction[Expr, Boolean]) {
      val result = checkCompSuccess(evaluator, in)
      if (!out.isDefinedAt(result) || !out(result))
        throw new AssertionError(s"Evaluation of '$in' with evaluator '${evaluator.name}' produced invalid '$result'.")
    }

    val ONE = bi(1)
    val TWO = bi(2)

    for(e <- allEvaluators) {
      checkLambda(e, fcall("Lambda.foo1")(), { 
        case Lambda(Seq(vd), Variable(id)) if vd.id == id => true 
      })
      checkLambda(e, fcall("Lambda.foo2")(), {
        case Lambda(Seq(vd), Plus(ONE, Variable(id))) if vd.id == id => true
      })
      checkLambda(e, fcall("Lambda.foo3")(), {
        case Lambda(Seq(vx, vy), Plus(Plus(Variable(x), ONE), Plus(Variable(y), TWO))) if vx.id == x && vy.id == y => true 
      })
      checkLambda(e, fcall("Lambda.foo4")(TWO), {
        case Lambda(Seq(vd), Plus(Variable(id), TWO)) if vd.id == id => true 
      })
    }
  }

  test("Methods") { implicit fix =>
    for(e <- allEvaluators) {
      // Some simple math.
      eval(e, fcall("Methods.f1")()) === T
      eval(e, fcall("Methods.f2")()) === F
      eval(e, fcall("Methods.f3")()) === T
    }
  }


  test("Literals") { implicit fix =>
    for(e <- allEvaluators) {
      eval(e, BooleanLiteral(true))         === BooleanLiteral(true)
      eval(e, BooleanLiteral(false))        === BooleanLiteral(false)
      eval(e, IntLiteral(0))                === IntLiteral(0)
      eval(e, IntLiteral(42))               === IntLiteral(42)
      eval(e, UnitLiteral())                === UnitLiteral()
      eval(e, InfiniteIntegerLiteral(0))    === InfiniteIntegerLiteral(0)
      eval(e, InfiniteIntegerLiteral(42))   === InfiniteIntegerLiteral(42)
      eval(e, RealLiteral(0))               === RealLiteral(0)
      eval(e, RealLiteral(42))              === RealLiteral(42)
      eval(e, RealLiteral(13.255))          === RealLiteral(13.255)
    }
  }

  test("BitVector Arithmetic") { implicit fix =>
    for(e <- allEvaluators) {
      eval(e, BVPlus(IntLiteral(3), IntLiteral(5)))  === IntLiteral(8)
      eval(e, BVPlus(IntLiteral(0), IntLiteral(5)))  === IntLiteral(5)
      eval(e, BVTimes(IntLiteral(3), IntLiteral(3))) === IntLiteral(9)
    }
  }

  test("eval bitwise operations") { implicit fix =>
    for(e <- allEvaluators) {
      eval(e, BVAnd(IntLiteral(3), IntLiteral(1))) === IntLiteral(1)
      eval(e, BVAnd(IntLiteral(3), IntLiteral(3))) === IntLiteral(3)
      eval(e, BVAnd(IntLiteral(5), IntLiteral(3))) === IntLiteral(1)
      eval(e, BVAnd(IntLiteral(5), IntLiteral(4))) === IntLiteral(4)
      eval(e, BVAnd(IntLiteral(5), IntLiteral(2))) === IntLiteral(0)

      eval(e, BVOr(IntLiteral(3), IntLiteral(1))) === IntLiteral(3)
      eval(e, BVOr(IntLiteral(3), IntLiteral(3))) === IntLiteral(3)
      eval(e, BVOr(IntLiteral(5), IntLiteral(3))) === IntLiteral(7)
      eval(e, BVOr(IntLiteral(5), IntLiteral(4))) === IntLiteral(5)
      eval(e, BVOr(IntLiteral(5), IntLiteral(2))) === IntLiteral(7)

      eval(e, BVXOr(IntLiteral(3), IntLiteral(1))) === IntLiteral(2)
      eval(e, BVXOr(IntLiteral(3), IntLiteral(3))) === IntLiteral(0)

      eval(e, BVNot(IntLiteral(1))) === IntLiteral(-2)

      eval(e, BVShiftLeft(IntLiteral(3), IntLiteral(1))) === IntLiteral(6)
      eval(e, BVShiftLeft(IntLiteral(4), IntLiteral(2))) === IntLiteral(16)

      eval(e, BVLShiftRight(IntLiteral(8), IntLiteral(1))) === IntLiteral(4)
      eval(e, BVAShiftRight(IntLiteral(8), IntLiteral(1))) === IntLiteral(4)
    }
  }

  test("Arithmetic 2") { implicit fix =>
    for(e <- allEvaluators) {
      eval(e, Plus(InfiniteIntegerLiteral(3), InfiniteIntegerLiteral(5)))  === InfiniteIntegerLiteral(8)
      eval(e, Minus(InfiniteIntegerLiteral(7), InfiniteIntegerLiteral(2))) === InfiniteIntegerLiteral(5)
      eval(e, UMinus(InfiniteIntegerLiteral(7)))                           === InfiniteIntegerLiteral(-7)
      eval(e, Times(InfiniteIntegerLiteral(2), InfiniteIntegerLiteral(3))) === InfiniteIntegerLiteral(6)
    }
  }

  test("BigInt Modulo and Remainder") { implicit fix =>
    for(e <- allEvaluators) {
      eval(e, Division(InfiniteIntegerLiteral(10), InfiniteIntegerLiteral(3)))   === InfiniteIntegerLiteral(3)
      eval(e, Remainder(InfiniteIntegerLiteral(10), InfiniteIntegerLiteral(3)))  === InfiniteIntegerLiteral(1)
      eval(e, Modulo(InfiniteIntegerLiteral(10), InfiniteIntegerLiteral(3)))     === InfiniteIntegerLiteral(1)

      eval(e, Division(InfiniteIntegerLiteral(-1), InfiniteIntegerLiteral(3)))   === InfiniteIntegerLiteral(0)
      eval(e, Remainder(InfiniteIntegerLiteral(-1), InfiniteIntegerLiteral(3)))  === InfiniteIntegerLiteral(-1)

      eval(e, Modulo(InfiniteIntegerLiteral(-1), InfiniteIntegerLiteral(3)))     === InfiniteIntegerLiteral(2)

      eval(e, Division(InfiniteIntegerLiteral(-1), InfiniteIntegerLiteral(-3)))  === InfiniteIntegerLiteral(0)
      eval(e, Remainder(InfiniteIntegerLiteral(-1), InfiniteIntegerLiteral(-3))) === InfiniteIntegerLiteral(-1)
      eval(e, Modulo(InfiniteIntegerLiteral(-1), InfiniteIntegerLiteral(-3)))    === InfiniteIntegerLiteral(2)

      eval(e, Division(InfiniteIntegerLiteral(1), InfiniteIntegerLiteral(-3)))   === InfiniteIntegerLiteral(0)
      eval(e, Remainder(InfiniteIntegerLiteral(1), InfiniteIntegerLiteral(-3)))  === InfiniteIntegerLiteral(1)
      eval(e, Modulo(InfiniteIntegerLiteral(1), InfiniteIntegerLiteral(-3)))     === InfiniteIntegerLiteral(1)
    }
  }

  test("Int Comparisons") { implicit fix =>
    for(e <- allEvaluators) {
      eval(e, GreaterEquals(InfiniteIntegerLiteral(7), InfiniteIntegerLiteral(4)))  === BooleanLiteral(true)
      eval(e, GreaterEquals(InfiniteIntegerLiteral(7), InfiniteIntegerLiteral(7)))  === BooleanLiteral(true)
      eval(e, GreaterEquals(InfiniteIntegerLiteral(4), InfiniteIntegerLiteral(7)))  === BooleanLiteral(false)

      eval(e, GreaterThan(InfiniteIntegerLiteral(7), InfiniteIntegerLiteral(4)))    === BooleanLiteral(true)
      eval(e, GreaterThan(InfiniteIntegerLiteral(7), InfiniteIntegerLiteral(7)))    === BooleanLiteral(false)
      eval(e, GreaterThan(InfiniteIntegerLiteral(4), InfiniteIntegerLiteral(7)))    === BooleanLiteral(false)

      eval(e, LessEquals(InfiniteIntegerLiteral(7), InfiniteIntegerLiteral(4)))     === BooleanLiteral(false)
      eval(e, LessEquals(InfiniteIntegerLiteral(7), InfiniteIntegerLiteral(7)))     === BooleanLiteral(true)
      eval(e, LessEquals(InfiniteIntegerLiteral(4), InfiniteIntegerLiteral(7)))     === BooleanLiteral(true)

      eval(e, LessThan(InfiniteIntegerLiteral(7), InfiniteIntegerLiteral(4)))       === BooleanLiteral(false)
      eval(e, LessThan(InfiniteIntegerLiteral(7), InfiniteIntegerLiteral(7)))       === BooleanLiteral(false)
      eval(e, LessThan(InfiniteIntegerLiteral(4), InfiniteIntegerLiteral(7)))       === BooleanLiteral(true)
    }
  }


  test("Int Modulo and Remainder") { implicit fix =>
    for(e <- allEvaluators) {
      eval(e, BVDivision(IntLiteral(10), IntLiteral(3)))    === IntLiteral(3)
      eval(e, BVRemainder(IntLiteral(10), IntLiteral(3)))   === IntLiteral(1)

      eval(e, BVDivision(IntLiteral(-1), IntLiteral(3)))    === IntLiteral(0)
      eval(e, BVRemainder(IntLiteral(-1), IntLiteral(3)))   === IntLiteral(-1)

      eval(e, BVDivision(IntLiteral(-1), IntLiteral(-3)))   === IntLiteral(0)
      eval(e, BVRemainder(IntLiteral(-1), IntLiteral(-3)))  === IntLiteral(-1)

      eval(e, BVDivision(IntLiteral(1), IntLiteral(-3)))    === IntLiteral(0)
      eval(e, BVRemainder(IntLiteral(1), IntLiteral(-3)))   === IntLiteral(1)
    }
  }

  test("Boolean Operations") { implicit fix =>
    for(e <- allEvaluators) {
      eval(e, And(BooleanLiteral(true), BooleanLiteral(true)))      === BooleanLiteral(true)
      eval(e, And(BooleanLiteral(true), BooleanLiteral(false)))     === BooleanLiteral(false)
      eval(e, And(BooleanLiteral(false), BooleanLiteral(false)))    === BooleanLiteral(false)
      eval(e, And(BooleanLiteral(false), BooleanLiteral(true)))     === BooleanLiteral(false)
      eval(e, Or(BooleanLiteral(true), BooleanLiteral(true)))       === BooleanLiteral(true)
      eval(e, Or(BooleanLiteral(true), BooleanLiteral(false)))      === BooleanLiteral(true)
      eval(e, Or(BooleanLiteral(false), BooleanLiteral(false)))     === BooleanLiteral(false)
      eval(e, Or(BooleanLiteral(false), BooleanLiteral(true)))      === BooleanLiteral(true)
      eval(e, Not(BooleanLiteral(false)))                           === BooleanLiteral(true)
      eval(e, Not(BooleanLiteral(true)))                            === BooleanLiteral(false)
    }
  }

  test("Real Arightmetic") { implicit fix =>
    for(e <- allEvaluators) {
      eval(e, RealPlus(RealLiteral(3), RealLiteral(5)))     === RealLiteral(8)
      eval(e, RealMinus(RealLiteral(7), RealLiteral(2)))    === RealLiteral(5)
      eval(e, RealUMinus(RealLiteral(7)))                   === RealLiteral(-7)
      eval(e, RealTimes(RealLiteral(2), RealLiteral(3)))    === RealLiteral(6)
      eval(e, RealPlus(RealLiteral(2.5), RealLiteral(3.5))) === RealLiteral(6)
    }
  }

  test("Real Comparisons") { implicit fix =>
    for(e <- allEvaluators) {
      eval(e, GreaterEquals(RealLiteral(7), RealLiteral(4))) === BooleanLiteral(true)
      eval(e, GreaterEquals(RealLiteral(7), RealLiteral(7))) === BooleanLiteral(true)
      eval(e, GreaterEquals(RealLiteral(4), RealLiteral(7))) === BooleanLiteral(false)

      eval(e, GreaterThan(RealLiteral(7), RealLiteral(4)))  === BooleanLiteral(true)
      eval(e, GreaterThan(RealLiteral(7), RealLiteral(7)))  === BooleanLiteral(false)
      eval(e, GreaterThan(RealLiteral(4), RealLiteral(7)))  === BooleanLiteral(false)

      eval(e, LessEquals(RealLiteral(7), RealLiteral(4)))   === BooleanLiteral(false)
      eval(e, LessEquals(RealLiteral(7), RealLiteral(7)))   === BooleanLiteral(true)
      eval(e, LessEquals(RealLiteral(4), RealLiteral(7)))   === BooleanLiteral(true)

      eval(e, LessThan(RealLiteral(7), RealLiteral(4)))     === BooleanLiteral(false)
      eval(e, LessThan(RealLiteral(7), RealLiteral(7)))     === BooleanLiteral(false)
      eval(e, LessThan(RealLiteral(4), RealLiteral(7)))     === BooleanLiteral(true)
    }
  }

  test("Simple Variable") { implicit fix =>
    for(e <- allEvaluators) {
      val id = FreshIdentifier("id", Int32Type)

      eval(e, Variable(id), Map(id -> IntLiteral(23))) === IntLiteral(23)
    }
  }

  test("Undefined Variable") { implicit fix =>
    for(e <- allEvaluators) {
      val id = FreshIdentifier("id", Int32Type)
      val foo = FreshIdentifier("foo", Int32Type)

      eval(e, Variable(id), Map(foo -> IntLiteral(23))).failed
    }
  }

  test("Let") { implicit fix =>
    for(e <- normalEvaluators) {
      val id = FreshIdentifier("id")
      eval(e, Let(id, IntLiteral(42), Variable(id))) === IntLiteral(42)
    }
  }


  def eqArray(a1: Expr, a2: Expr) = (a1, a2) match {
    case (FiniteArray(es1, d1, IntLiteral(l1)), FiniteArray(es2, d2, IntLiteral(l2))) =>
      assert(l1 === l2)
      for (i <- 0 until l1) {
        val v1 = es1.get(i).orElse(d1)
        val v2 = es2.get(i).orElse(d2)
        assert(v1 === v2)
      }
    case (e, _) =>
      fail("Expected array, got "+e)
  }

  test("Array Operations") { implicit fix =>
    for (e <- allEvaluators) {
      eqArray(eval(e, finiteArray(Map[Int,Expr](), Some(IntLiteral(12), IntLiteral(7)), Int32Type)).res,
                      finiteArray(Map[Int,Expr](), Some(IntLiteral(12), IntLiteral(7)), Int32Type))

      eval(e, ArrayLength(finiteArray(Map[Int,Expr](), Some(IntLiteral(12), IntLiteral(7)), Int32Type))) ===
                      IntLiteral(7)

      eval(e, ArraySelect(finiteArray(Seq(IntLiteral(2), IntLiteral(4), IntLiteral(7))), IntLiteral(1))) ===
                      IntLiteral(4)

      eqArray(eval(e, ArrayUpdated( finiteArray(Seq(IntLiteral(2), IntLiteral(4), IntLiteral(7))), IntLiteral(1), IntLiteral(42))).res,
                      finiteArray(Seq(IntLiteral(2), IntLiteral(42), IntLiteral(7))))

    }
  }

  test("Array with variable length") { implicit fix =>
    // This does not work with CodegenEvaluator
    for (e <- normalEvaluators) {
      val len = FreshIdentifier("len", Int32Type)
      eval(e, ArrayLength(finiteArray(Map[Int, Expr](), Some(IntLiteral(12), Variable(len)), Int32Type)), Map(len -> IntLiteral(27))) ===
        IntLiteral(27)
    }
  }

  test("Array Default Value") { implicit fix  =>
    for (e <- allEvaluators) {
      val id = FreshIdentifier("id", Int32Type)
      eqArray(eval(e, finiteArray(Map[Int, Expr](), Some(Variable(id), IntLiteral(7)), Int32Type), Map(id -> IntLiteral(27))).res, 
                      finiteArray(Map[Int, Expr](), Some(IntLiteral(27), IntLiteral(7)), Int32Type))
    }
  }

  private def checkCompSuccess(evaluator: Evaluator, in: Expr): Expr = {
    import EvaluationResults._

    evaluator.eval(in) match {
      case RuntimeError(msg) =>
        throw new AssertionError(s"Evaluation of '$in' with evaluator '${evaluator.name}' should have succeeded, but it failed ($msg).")

      case EvaluatorError(msg) =>
        throw new AssertionError(s"Evaluation of '$in' with evaluator '${evaluator.name}' should have succeeded, but the evaluator had an internal error ($msg).")

      case Successful(result) =>
        result
    }
  }

  abstract class EvalDSL {
    def res: Expr
    def ===(res: Expr): Unit
    def failed: Unit = {}
    def success: Unit = {}
  }

  case class Success(expr: Expr, env: Map[Identifier, Expr], evaluator: Evaluator, res: Expr) extends EvalDSL {
    override def failed = {
      fail(s"Evaluation of '$expr' with '$evaluator' (and env $env) should have failed")
    }

    def ===(exp: Expr) = {
      assert(res === exp)
    }
  }

  case class Failed(expr: Expr, env: Map[Identifier, Expr], evaluator: Evaluator, err: String) extends EvalDSL {
    override def success = {
      fail(s"Evaluation of '$expr' with '$evaluator' (and env $env) should have succeeded but failed with $err")
    }

    def res = success

    def ===(res: Expr) = success
  }

  def eval(e: Evaluator, toEval: Expr, env: Map[Identifier, Expr] = Map()): EvalDSL = {
    e.eval(toEval, env) match {
      case EvaluationResults.Successful(res)     => Success(toEval, env, e, res)
      case EvaluationResults.RuntimeError(err)   => Failed(toEval, env, e, err)
      case EvaluationResults.EvaluatorError(err) => Failed(toEval, env, e, err)
    }
  }
}
