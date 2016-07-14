/* Copyright 2009-2016 EPFL, Lausanne */

package leon.integration.evaluators

import leon._
import leon.test._
import leon.test.helpers._
import leon.evaluators.{Evaluator => _, DeterministicEvaluator => Evaluator, _}
import leon.purescala.Common._
import leon.purescala.Definitions._
import leon.purescala.Expressions._
import leon.purescala.Types._
import leon.codegen._

class EvaluatorSuite extends LeonTestSuiteWithProgram with ExpressionsDSL {

  val sources = List(
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
       |  def add(s1 : Set[Int], e: Int) : Set[Int] = s1 + e
       |  def union(s1 : Set[Int], s2 : Set[Int]) : Set[Int] = s1 ++ s2
       |  def inter(s1 : Set[Int], s2 : Set[Int]) : Set[Int] = s1 & s2
       |  def diff(s1 : Set[Int], s2 : Set[Int]) : Set[Int] = s1 -- s2
       |}""".stripMargin,

    """|import leon.lang._
       |object Bags {
       |  sealed abstract class List
       |  case class Nil() extends List
       |  case class Cons(head : Int, tail : List) extends List
       |
       |  def content(l : List) : Bag[Int] = l match {
       |    case Nil() => Bag.empty[Int]
       |    case Cons(x, xs) => content(xs) + x
       |  }
       |
       |  def finite() : Bag[Int] = Bag((1, 1), (2, 2), (3, 3))
       |  def add(s1 : Bag[Int], e: Int) : Bag[Int] = s1 + e
       |  def union(s1 : Bag[Int], s2 : Bag[Int]) : Bag[Int] = s1 ++ s2
       |  def inter(s1 : Bag[Int], s2 : Bag[Int]) : Bag[Int] = s1 & s2
       |  def diff(s1 : Bag[Int], s2 : Bag[Int]) : Bag[Int] = s1 -- s2
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
      |}""".stripMargin,

    """import leon.lang._
      |import leon.collection._
      |
      |object Foo {
      |  def unapply(i: BigInt): Option[BigInt] = if (i > 0) Some(i) else None()
      |}
      |
      |object Unapply {
      |  def foo =
      |    (BigInt(1) match {
      |      case Foo(i) => i
      |      case _ => BigInt(0)
      |    }) + (BigInt(-12) match {
      |      case Foo(i) => i
      |      case _ => BigInt(2)
      |    })
      |
      |  def size[A](l: List[A]): BigInt = l match {
      |    case _ :: _ :: _ :: Nil() => 3
      |    case _ :: _ :: Nil() => 2
      |    case _ :: Nil() => 1
      |    case Nil() => 0
      |    case _ :: _ => 42
      |  }
      |
      |  def s1 = size(1 :: 2 :: 3 :: Nil[Int]())
      |  def s2 = size(Nil[Int]())
      |  def s3 = size(List(1,2,3,4,5,6,7,8))
      |
      |}
    """.stripMargin,

    """object Casts1 {
      |  abstract class Foo
      |  case class Bar1(v: BigInt) extends Foo
      |  case class Bar2(v: BigInt) extends Foo
      |  case class Bar3(v: BigInt) extends Foo
      |
      |  def test(a: Foo): BigInt = {
      |    if (a.isInstanceOf[Bar1]) {
      |      a.asInstanceOf[Bar1].v
      |    } else {
      |      a.asInstanceOf[Bar2].v
      |    }
      |  }
      |}""".stripMargin
  )

  def normalEvaluators(implicit ctx: LeonContext, pgm: Program): List[Evaluator] = {
    List(
      new DefaultEvaluator(ctx, pgm),
      new AngelicEvaluator(new StreamEvaluator(ctx, pgm))
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
      eval(e, fcall("Sets.add")(s12, i(2)))          === s12
      eval(e, fcall("Sets.add")(s12, i(3)))          === s123
      eval(e, fcall("Sets.union")(s123, s246))       === s12346
      eval(e, fcall("Sets.union")(s246, s123))       === s12346
      eval(e, fcall("Sets.inter")(s123, s246))       === s2
      eval(e, fcall("Sets.inter")(s246, s123))       === s2
      eval(e, fcall("Sets.diff")(s123, s246))        === s13
      eval(e, fcall("Sets.diff")(s246, s123))        === s46

      eval(e, Equals(fcall("Sets.union")(s123, s246), fcall("Sets.union")(s246, s123))) === T
      eval(e, Equals(fcall("Sets.inter")(s123, s246), fcall("Sets.inter")(s246, s123))) === T
      eval(e, Equals(fcall("Sets.diff")(s123, s246),  fcall("Sets.diff")(s246, s123)))   === F
    }
  }

  test("Bags") { implicit fix  =>
    val nil = cc("Bags.Nil")()
    def cons(es: Expr*) = cc("Bags.Cons")(es: _*)

    val cons12 = cons(i(1), cons(i(2), nil))
    val cons122 = cons(i(1), cons(i(2), cons(i(2), nil)))

    def fb(is: (Int, Int)*) = FiniteBag(is.map(p => i(p._1) -> bi(p._2)).toMap, Int32Type)

    val b12    = fb(1 -> 1, 2 -> 1)
    val b123   = fb(1 -> 1, 2 -> 1, 3 -> 1)
    val b246   = fb(2 -> 1, 4 -> 1, 6 -> 1)
    val b1223  = fb(1 -> 1, 2 -> 2, 3 -> 1)

    for(e <- allEvaluators) {
      eval(e, fcall("Bags.finite")())                === fb(1 -> 1, 2 -> 2, 3 -> 3)
      eval(e, fcall("Bags.content")(nil))            === fb()
      eval(e, fcall("Bags.content")(cons12))         === fb(1 -> 1, 2 -> 1)
      eval(e, fcall("Bags.content")(cons122))        === fb(1 -> 1, 2 -> 2)
      eval(e, fcall("Bags.add")(b12, i(2)))          === fb(1 -> 1, 2 -> 2)
      eval(e, fcall("Bags.add")(b12, i(3)))          === fb(1 -> 1, 2 -> 1, 3 -> 1)
      eval(e, fcall("Bags.union")(b123, b246))       === fb(1 -> 1, 2 -> 2, 3 -> 1, 4 -> 1, 6 -> 1)
      eval(e, fcall("Bags.union")(b246, b123))       === fb(1 -> 1, 2 -> 2, 3 -> 1, 4 -> 1, 6 -> 1)
      eval(e, fcall("Bags.inter")(b123, b246))       === fb(2 -> 1)
      eval(e, fcall("Bags.inter")(b246, b123))       === fb(2 -> 1)
      eval(e, fcall("Bags.inter")(b1223, b123))      === b123
      eval(e, fcall("Bags.diff")(b123, b246))        === fb(1 -> 1, 3 -> 1)
      eval(e, fcall("Bags.diff")(b246, b123))        === fb(4 -> 1, 6 -> 1)
      eval(e, fcall("Bags.diff")(b1223, b123))       === fb(2 -> 1)
      eval(e, fcall("Bags.diff")(b123, b1223))       === fb()
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
    val e = new CodeGenEvaluator(fix._1, fix._2, params = CodeGenParams.default.copy(maxFunctionInvocations = 32))

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
    for(e <- allEvaluators) {
      eval(e, Application(fcall("Lambda.foo1")(), Seq(bi(1))))        === bi(1)
      eval(e, Application(fcall("Lambda.foo2")(), Seq(bi(1))))        === bi(2)
      eval(e, Application(fcall("Lambda.foo3")(), Seq(bi(1), bi(2)))) === bi(6)
      eval(e, Application(fcall("Lambda.foo4")(bi(2)), Seq(bi(1))))   === bi(3)
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

  test("Unapply") { implicit fix =>
    for(e <- allEvaluators) {
      eval(e, fcall("Unapply.foo")()) === bi(3)
      eval(e, fcall("Unapply.s1")())  === bi(3)
      eval(e, fcall("Unapply.s2")())  === bi(0)
      eval(e, fcall("Unapply.s3")())  === bi(42)
    }
  }

  test("Casts1") { implicit fix =>
    def bar1(es: Expr*) = cc("Casts1.Bar1")(es: _*)
    def bar2(es: Expr*) = cc("Casts1.Bar2")(es: _*)
    def bar3(es: Expr*) = cc("Casts1.Bar3")(es: _*)

    val b42 = bi(42)

    for(e <- allEvaluators) {
      eval(e, fcall("Casts1.test")(bar1(b42))) === b42
      eval(e, fcall("Casts1.test")(bar2(b42))) === b42
      eval(e, fcall("Casts1.test")(bar3(b42))).failed
    }
  }

  abstract class EvalDSL {
    def res: Expr
    def ===(res: Expr): Unit
    def failed: Unit = {}
    def success: Expr = res
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
