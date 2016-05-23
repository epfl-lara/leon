/* Copyright 2009-2015 EPFL, Lausanne */

package leon.unit.orb

import leon._
import leon.test._
import leon.purescala.Expressions._
import leon.purescala.Types._
import leon.purescala.Common._
import leon.purescala.ExprOps._
import leon.invariant.util.LetTupleSimplification
import scala.math.BigInt.int2bigInt
import leon.purescala.Definitions._
import leon.invariant.engine._
import leon.transformations._
import java.io.File
import leon.purescala.Types.TupleType
import leon.utils._
import invariant.structure.LinearConstraintUtil._
import leon.invariant.util.ExpressionTransformer._
import invariant.structure._
import invariant.util._
import ProgramUtil._
import Util.zero

class OrbUnitTestSuite extends LeonTestSuite {
  val a = FreshIdentifier("a", IntegerType).toVariable
  val b = FreshIdentifier("b", IntegerType).toVariable
  val c = FreshIdentifier("c", IntegerType).toVariable
  val d = FreshIdentifier("d", IntegerType).toVariable
  val l42 = InfiniteIntegerLiteral(42)
  val l43 = InfiniteIntegerLiteral(43)
  val mtwo = InfiniteIntegerLiteral(-2)

  test("Pull lets to top with tuples and tuple select") { ctx =>
    val in  = TupleSelect(Tuple(Seq(a, b)), 1)
    val exp = in
    val out = LetTupleSimplification.removeLetsFromLetValues(in)
    assert(out === exp)
  }

  test("TestElimination") {ctx =>
    val exprs = Seq(Equals(a, b), Equals(c, Plus(a, b)), GreaterEquals(Plus(c, d), zero))
    //println("Exprs: "+exprs)
    val retainVars = Set(d).map(_.id)
    val ctrs = exprs map ConstraintUtil.createConstriant
    val nctrs = apply1PRuleOnDisjunct(ctrs.collect{ case c: LinearConstraint => c }, retainVars, None)
    //println("Constraints after elimination: "+nctrs)
    assert(nctrs.size == 1)
  }

  test("TestElimination2") {ctx =>
    val exprs = Seq(Equals(zero, Plus(a, b)), Equals(a, zero), GreaterEquals(Plus(b, c), zero))
    //println("Exprs: "+exprs)
    val retainVars = Set(c).map(_.id)
    val ctrs = exprs map ConstraintUtil.createConstriant
    val nctrs = apply1PRuleOnDisjunct(ctrs.collect{ case c: LinearConstraint => c }, retainVars, None)
    //println("Constraints after elimination: "+nctrs)
    assert(nctrs.size == 1)
  }

  def createLeonContext(opts: String*): LeonContext = {
    val reporter = new TestSilentReporter
    Main.processOptions(opts.toList).copy(reporter = reporter, interruptManager = new InterruptManager(reporter))
  }

  def scalaExprToTree(scalaExpr: String): Expr = {
    val ctx = createLeonContext()
    val testFilename = toTempFile(s"""
      import leon.annotation._
    	object Test { def test() = { $scalaExpr } }""")
    val beginPipe = leon.frontends.scalac.ExtractionPhase andThen
      new leon.utils.PreprocessingPhase
    val (_, program) = beginPipe.run(ctx, testFilename)
    //println("Program: "+program)
    functionByName("test", program).get.body.get
  }

  def toTempFile(content: String): List[String] = {
    TemporaryInputPhase.run(createLeonContext(), (List(content), Nil))._2
  }
}
