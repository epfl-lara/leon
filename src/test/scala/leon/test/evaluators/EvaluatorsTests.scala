/* Copyright 2009-2014 EPFL, Lausanne */

package leon.test.evaluators

import leon._
import leon.evaluators._ 

import leon.utils.{TemporaryInputPhase, PreprocessingPhase}
import leon.frontends.scalac.ExtractionPhase

import leon.purescala.Common._
import leon.purescala.Definitions._
import leon.purescala.Trees._
import leon.purescala.DefOps._
import leon.purescala.TypeTrees._
import leon.purescala.Extractors._
import leon.purescala.Constructors._

class EvaluatorsTests extends leon.test.LeonTestSuite {
  private implicit lazy val leonContext = testContext

  private val evaluatorConstructors : List[(LeonContext,Program)=>Evaluator] = List(
    new DefaultEvaluator(_,_),
    new CodeGenEvaluator(_,_)
  )

  private def prepareEvaluators(implicit ctx : LeonContext, prog : Program) : List[Evaluator] = evaluatorConstructors.map(c => c(leonContext, prog))

  private def parseString(str : String) : Program = {
    val pipeline = TemporaryInputPhase andThen ExtractionPhase andThen PreprocessingPhase

    val errorsBefore   = leonContext.reporter.errorCount
    val warningsBefore = leonContext.reporter.warningCount

    val program = pipeline.run(leonContext)((str, Nil))

    assert(leonContext.reporter.errorCount   === errorsBefore)

    program
  }

  private def mkCall(name : String, args : Expr*)(implicit p : Program) = {
    val fn = s"Program.$name"

    searchByFullName(fn, p) match {
      case Some(fd: FunDef) =>
        FunctionInvocation(fd.typed, args.toSeq)
      case _ =>
        throw new AssertionError("No function named '%s' defined in program.".format(fn))
    }
  }

  private def mkCaseClass(name : String, args : Expr*)(implicit p : Program) = {
    searchByFullName("Program."+name, p) match {
      case Some(ccd: CaseClassDef) =>
        CaseClass(CaseClassType(ccd, Nil), args.toSeq)
      case _ =>
        throw new AssertionError("No case class named '%s' defined in program.".format(name))
    }
  }

  private def checkCompSuccess(evaluator : Evaluator, in : Expr) : Expr = {
    import EvaluationResults._

    evaluator.eval(in) match {
      case RuntimeError(msg) =>
        throw new AssertionError("Evaluation of '%s' with evaluator '%s' should have succeeded, but it failed (%s).".format(in, evaluator.name, msg))

      case EvaluatorError(msg) =>
        throw new AssertionError("Evaluation of '%s' with evaluator '%s' should have succeeded, but the evaluator had an internal error (%s).".format(in, evaluator.name, msg))

      case Successful(result) =>
        result
    }
  }

  private def checkComp(evaluator : Evaluator, in : Expr, out : Expr) {
    val result = checkCompSuccess(evaluator, in)
    if(result != out)
      throw new AssertionError("Evaluation of '%s' with evaluator '%s' should have produced '%s' but produced '%s' instead.".format(in, evaluator.name, out, result))
  }

  private def checkSetComp(evaluator : Evaluator, in : Expr, out : Set[Int]) {
    val result = checkCompSuccess(evaluator, in)

    def asIntSet(e : Expr) : Option[Set[Int]] = e match {
      case FiniteSet(es) =>
        val ois = es.map(_ match {
          case IntLiteral(v) => Some(v)
          case _ => None
        })
        if(ois.forall(_.isDefined))
          Some(ois.map(_.get).toSet)
        else
          None
      case _ => None
    }

    asIntSet(result) match {
      case Some(s) if s == out =>
        ;

      case _ =>
        throw new AssertionError("Evaluation of '%s' with evaluator '%s' should have produced a set '%s', but it produced '%s' instead.".format(in, evaluator.name, out, result))
    }
  }

  private def checkMapComp(evaluator : Evaluator, in : Expr, out : Map[Int,Int]) {
    val result = checkCompSuccess(evaluator, in)

    def asIntMap(e : Expr) : Option[Map[Int,Int]] = e match {
      case FiniteMap(ss) =>
        val oips : Seq[Option[(Int,Int)]] = ss.map(_ match {
          case (IntLiteral(f),IntLiteral(t)) => Some(f -> t)
          case _ => None
        })
        if(oips.forall(_.isDefined))
          Some(oips.map(_.get).toMap)
        else
          None
      case _ => None
    }

    asIntMap(result) match {
      case Some(s) if s == out =>
        ;

      case _ =>
        throw new AssertionError("Evaluation of '%s' with evaluator '%s' should produced a map '%s', but it produced '%s' instead.".format(in, evaluator.name, out, result))
    }
  }

  private def checkError(evaluator : Evaluator, in : Expr) {
    import EvaluationResults._

    evaluator.eval(in) match {
      case EvaluatorError(msg) =>
        throw new AssertionError("Evaluation of '%s' with evaluator '%s' should have failed, but it produced an internal error (%s).".format(in, evaluator.name, msg))

      case Successful(result) =>
        throw new AssertionError("Evaluation of '%s' with evaluator '%s' should have failed, but it produced the result '%s' instead.".format(in, evaluator.name, result))

      case RuntimeError(_) =>
        // that's the desired outcome
    }
  }

  private def checkEvaluatorError(evaluator : Evaluator, in : Expr) {
    import EvaluationResults._

    evaluator.eval(in) match {
      case RuntimeError(msg) =>
        throw new AssertionError("Evaluation of '%s' with evaluator '%s' should have produced an internal error, but it failed instead (%s).".format(in, evaluator.name, msg))

      case Successful(result) =>
        throw new AssertionError("Evaluation of '%s' with evaluator '%s' should have produced an internal error, but it produced the result '%s' instead.".format(in, evaluator.name, result))

      case EvaluatorError(_) =>
        // that's the desired outcome
    }
  }

  private def T = BooleanLiteral(true)
  private def F = BooleanLiteral(false)
  private def IL(i : Int) = IntLiteral(i)

  test("Arithmetic") {
    val p = """|object Program {
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
               |  def mod(x : Int, y : Int) : Int = (x % y)
               |}
               |""".stripMargin

    implicit val prog = parseString(p)
    val evaluators = prepareEvaluators

    for(e <- evaluators) {
      // Some simple math.
      checkComp(e, mkCall("plus", IL(60), BVUMinus(IL(18))), IL(42))
      checkComp(e, mkCall("max", IL(4), IL(42)), IL(42))
      checkComp(e, mkCall("max", IL(42), BVUMinus(IL(42))), IL(42))
      checkComp(e, mkCall("intSqrt", BVUMinus(IL(1800))), IL(42))
      checkComp(e, mkCall("div", IL(7), IL(5)), IL(1))
      checkComp(e, mkCall("div", IL(7), IL(-5)), IL(-1))
      checkComp(e, mkCall("div", IL(-7), IL(5)), IL(-1))
      checkComp(e, mkCall("div", IL(-7), IL(-5)), IL(1))
      checkComp(e, mkCall("mod", IL(7), IL(5)), IL(2))
      checkComp(e, mkCall("mod", IL(7), IL(-5)), IL(2))
      checkComp(e, mkCall("mod", IL(-7), IL(5)), IL(-2))
      checkComp(e, mkCall("mod", IL(-7), IL(-5)), IL(-2))

      // Things that should crash.
      checkError(e, mkCall("div", IL(42), IL(0))) 
      checkError(e, mkCall("mod", IL(42), IL(0)))
    }
  }

  test("Booleans") {
    val p = """|object Program {
               |def and1(x : Boolean, y : Boolean) : Boolean = x && y
               |def or1(x : Boolean, y : Boolean)  : Boolean = x || y
               |def and2(x : Boolean, y : Boolean) : Boolean = !(!x || !y)
               |def or2(x : Boolean, y : Boolean)  : Boolean = !(!x && !y)
               |def safe(n : Int) : Boolean = (n != 0 && (1/n == n))
               |def mkTrue() : Boolean = true
               |def mkFalse() : Boolean = false
               |}""".stripMargin

    implicit val prog = parseString(p)
    val evaluators = prepareEvaluators

    for(e <- evaluators) {
      checkComp(e, mkCall("and1", F, F), F)
      checkComp(e, mkCall("and1", F, T), F)
      checkComp(e, mkCall("and1", T, F), F)
      checkComp(e, mkCall("and1", T, T), T)
      checkComp(e, mkCall("and2", F, F), F)
      checkComp(e, mkCall("and2", F, T), F)
      checkComp(e, mkCall("and2", T, F), F)
      checkComp(e, mkCall("and2", T, T), T)
      checkComp(e, mkCall("or1", F, F), F)
      checkComp(e, mkCall("or1", F, T), T)
      checkComp(e, mkCall("or1", T, F), T)
      checkComp(e, mkCall("or1", T, T), T)
      checkComp(e, mkCall("or2", F, F), F)
      checkComp(e, mkCall("or2", F, T), T)
      checkComp(e, mkCall("or2", T, F), T)
      checkComp(e, mkCall("or2", T, T), T)

      checkComp(e, mkCall("safe", IL(1)), T)
      checkComp(e, mkCall("safe", IL(2)), F)

      // This one needs short-circuit.
      checkComp(e, mkCall("safe", IL(0)), F)

      // We use mkTrue/mkFalse to avoid automatic simplifications.
      checkComp(e, Equals(mkCall("mkTrue"),  mkCall("mkTrue")),  T)
      checkComp(e, Equals(mkCall("mkTrue"),  mkCall("mkFalse")), F)
      checkComp(e, Equals(mkCall("mkFalse"), mkCall("mkTrue")),  F)
      checkComp(e, Equals(mkCall("mkFalse"), mkCall("mkFalse")), T)

      checkComp(e, Implies(mkCall("mkTrue"),  mkCall("mkTrue")),  T)
      checkComp(e, Implies(mkCall("mkTrue"),  mkCall("mkFalse")), F)
      checkComp(e, Implies(mkCall("mkFalse"), mkCall("mkTrue")),  T)
      checkComp(e, Implies(mkCall("mkFalse"), mkCall("mkFalse")), T)
    }
  }

  test("Case classes") {
    val p = """|object Program {
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
               |}""".stripMargin

    implicit val prog = parseString(p)
    val evaluators = prepareEvaluators

    val nil = mkCaseClass("Nil")
    val cons12a = mkCaseClass("Cons", IL(1), mkCaseClass("Cons", IL(2), mkCaseClass("Nil")))
    val cons12b = mkCaseClass("Cons", IL(1), mkCaseClass("Cons", IL(2), mkCaseClass("Nil")))
    val sing1 = mkCaseClass("MySingleton", IL(1))
    val sing2 = mkCaseClass("MySingleton", IL(2))

    for(e <- evaluators) {
      checkComp(e, mkCall("size", nil), IL(0))
      checkComp(e, mkCall("size", cons12a), IL(2))
      checkComp(e, mkCall("compare", nil, cons12a), F)
      checkComp(e, mkCall("compare", cons12a, cons12b), T)
      checkComp(e, mkCall("head", cons12a), IL(1))

      checkComp(e, Equals(mkCall("wrap", IL(1)), sing1), T)

      // Match error
      checkError(e, mkCall("head", nil))
    }
  }

  test("Sets") {
    val p = """|object Program {
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
               |}""".stripMargin

    implicit val prog = parseString(p)
    val evaluators = prepareEvaluators

    val nil = mkCaseClass("Nil")
    val cons12 = mkCaseClass("Cons", IL(1), mkCaseClass("Cons", IL(2), mkCaseClass("Nil")))

    val semp = EmptySet(Int32Type)
    val s123 = NonemptySet(Set(IL(1), IL(2), IL(3)))
    val s246 = NonemptySet(Set(IL(2), IL(4), IL(6)))

    for(e <- evaluators) {
      checkSetComp(e, mkCall("finite"), Set(1, 2, 3))
      checkSetComp(e, mkCall("content", nil), Set.empty)
      checkSetComp(e, mkCall("content", cons12), Set(1,2))
      checkSetComp(e, mkCall("build", IL(1), IL(2), IL(3)), Set(1,2,3))
      checkSetComp(e, mkCall("build", IL(1), IL(2), IL(2)), Set(1,2))
      checkSetComp(e, mkCall("union", s123, s246), Set(1,2,3,4,6))
      checkSetComp(e, mkCall("union", s246, s123), Set(1,2,3,4,6))
      checkComp(e, Equals(mkCall("union", s123, s246), mkCall("union", s246, s123)), T)
      checkSetComp(e, mkCall("inter", s123, s246), Set(2))
      checkSetComp(e, mkCall("inter", s246, s123), Set(2))
      checkComp(e, Equals(mkCall("inter", s123, s246), mkCall("inter", s246, s123)), T)
      checkSetComp(e, mkCall("diff", s123, s246), Set(1,3))
      checkSetComp(e, mkCall("diff", s246, s123), Set(4,6))
      checkComp(e, Equals(mkCall("diff", s123, s246), mkCall("diff", s246, s123)), F)
    }
  }

  test("Maps") {
    val p = """|object Program {
               |sealed abstract class PList
               |case class PNil() extends PList
               |case class PCons(headfst : Int, headsnd : Int, tail : PList) extends PList
               |
               |def toMap(pl : PList) : Map[Int,Int] = pl match {
               |  case PNil() => Map.empty[Int,Int]
               |  case PCons(f,s,xs) => toMap(xs).updated(f, s)
               |}
               |
               |def finite0() : Map[Int,Int] = Map[Int, Int]()
               |def finite1() : Map[Int,Int] = Map(1 -> 2)
               |def finite2() : Map[Int,Int] = Map(2 -> 3, 1 -> 2)
               |def finite3() : Map[Int,Int] = finite1().updated(2, 3)
               |}""".stripMargin

    implicit val prog = parseString(p)
    val evaluators = prepareEvaluators

    val cons1223 = mkCaseClass("PCons", IL(1), IL(2), mkCaseClass("PCons", IL(2), IL(3), mkCaseClass("PNil")))

    for(e <- evaluators) {
      checkMapComp(e, mkCall("finite0"), Map.empty)
      checkMapComp(e, mkCall("finite1"), Map(1 -> 2))
      checkMapComp(e, mkCall("finite2"), Map(1 -> 2, 2 -> 3))
      checkComp(e, Equals(mkCall("finite1"), mkCall("finite2")), F)
      checkComp(e, Equals(mkCall("finite2"), mkCall("finite3")), T)
      checkMapComp(e, mkCall("toMap", cons1223), Map(1 -> 2, 2 -> 3))
      checkComp(e, MapIsDefinedAt(mkCall("finite2"), IL(2)), T)
      checkComp(e, MapIsDefinedAt(mkCall("finite2"), IL(3)), F)
    }
  }

  test("Arrays") {
    val p = """|object Program {
               |  def boolArrayRead(bools : Array[Boolean], index : Int) : Boolean = bools(index)
               |
               |  def intArrayRead(ints : Array[Int], index : Int) : Int = ints(index)
               |
               |  def intArrayUpdate(ints : Array[Int], index : Int, value: Int) : Int = {
               |    val na = ints.updated(index, value)
               |    na(index)
               |  }
               |}
               |""".stripMargin

    implicit val progs = parseString(p)
    val evaluators = prepareEvaluators
    
    val ba = finiteArray(Seq(T, F))
    val ia = finiteArray(Seq(IL(41), IL(42), IL(43)))

    for(e <- evaluators) {
      checkComp(e, mkCall("boolArrayRead", ba, IL(0)), T)
      checkComp(e, mkCall("boolArrayRead", ba, IL(1)), F)
      checkComp(e, mkCall("intArrayRead", ia, IL(0)), IL(41))
      checkComp(e, mkCall("intArrayRead", ia, IL(1)), IL(42))
      checkComp(e, ArrayLength(ia), IL(3))

      checkComp(e, mkCall("intArrayUpdate", ia, IL(0), IL(13)), IL(13))
      checkComp(e, mkCall("intArrayUpdate", ia, IL(1), IL(17)), IL(17))

      checkError(e, mkCall("boolArrayRead", ba, IL(2)))
    }
  }

  test("Sets and maps of structures") {
    val p = """|object Program {
               |  case class MyPair(x : Int, y : Boolean)
               |
               |  def buildPairCC(x : Int, y : Boolean) : MyPair = MyPair(x,y)
               |  def mkSingletonCC(p : MyPair) : Set[MyPair] = Set(p)
               |  def containsCC(s : Set[MyPair], p : MyPair) : Boolean = s.contains(p)
               |
               |  def buildPairT(x : Int, y : Boolean) : (Int,Boolean) = (x,y)
               |  def mkSingletonT(p : (Int,Boolean)) : Set[(Int,Boolean)] = Set(p)
               |  def containsT(s : Set[(Int,Boolean)], p : (Int,Boolean)) : Boolean = s.contains(p)
               |}""".stripMargin

    implicit val progs = parseString(p)
    val evaluators = prepareEvaluators

    for(e <- evaluators) {
      checkComp(e, mkCall("containsCC", mkCall("mkSingletonCC", mkCall("buildPairCC", IL(42), T)), mkCall("buildPairCC", IL(42), T)), T)
      checkComp(e, mkCall("containsT", mkCall("mkSingletonT", mkCall("buildPairT", IL(42), T)), mkCall("buildPairT", IL(42), T)), T)
    }
  }

  test("Executing Chooses") {
    val p = """|object Program {
               |  import leon.lang._
               |  import leon.lang.synthesis._
               |
               |  def c(i : Int) : Int = choose { (j : Int) => j > i && j < i + 2 }
               |}
               |""".stripMargin

    implicit val prog = parseString(p)
    val evaluators = prepareEvaluators

    for(e <- evaluators) {
      checkComp(e, mkCall("c", IL(42)), IL(43))
    }
  }

  test("Infinite Recursion") {
    import leon.codegen._

    val p = """|object Program {
               |  import leon.lang._
               |
               |  def c(i : Int) : Int = c(i-1)
               |}
               |""".stripMargin

    implicit val prog = parseString(p)

    val e = new CodeGenEvaluator(leonContext, prog, CodeGenParams(maxFunctionInvocations = 32))
    checkEvaluatorError(e, mkCall("c", IL(42)))
  }

  test("Wrong Contracts") {
    import leon.codegen._

    val p = """|object Program {
               |  import leon.lang._
               |
               |  def c(i : Int) : Int = {
               |    require(i > 0);
               |    c(i-1)
               |  }
               |}
               |""".stripMargin

    implicit val prog = parseString(p)

    val e = new CodeGenEvaluator(leonContext, prog, CodeGenParams(checkContracts = true))
    checkError(e, mkCall("c", IL(-42)))
  }

  test("Pattern Matching") {
    val p = """|object Program {
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
               |}""".stripMargin

    implicit val prog = parseString(p)
    val evaluators = prepareEvaluators

    for(e <- evaluators) {
      // Some simple math.
      checkComp(e, mkCall("f1"), IL(1))
      checkComp(e, mkCall("f2"), IL(1))
      checkComp(e, mkCall("f3"), IL(1))
      checkComp(e, mkCall("f4"), IL(1))
      checkComp(e, mkCall("f5"), IL(1))
      checkComp(e, mkCall("f6"), IL(1))
    }
  }
}
