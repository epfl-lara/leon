/* Copyright 2009-2016 EPFL, Lausanne */

package leon.unit.xlang

import org.scalatest._

import leon.test._
import leon.purescala.Common._
import leon.purescala.Expressions._
import leon.purescala.Types._
import leon.purescala.TypeOps.isSubtypeOf
import leon.purescala.Definitions._
import leon.xlang.AliasAnalysis
import leon.xlang.Expressions._
import leon.xlang.ExprOps._

class AliasAnalysisSuite extends FunSuite with helpers.ExpressionsDSL {

  private val fd1 = new FunDef(FreshIdentifier("f1"), Seq(), Seq(ValDef(x.id)), IntegerType)
  fd1.body = Some(x)

  private val fd2 = new FunDef(FreshIdentifier("f2"), Seq(), Seq(ValDef(x.id)), IntegerType)
  fd2.body = Some(FunctionInvocation(fd1.typed, List(bi(1))))

  private val rec1 = new FunDef(FreshIdentifier("rec1"), Seq(), Seq(ValDef(x.id)), IntegerType)
  rec1.body = Some(FunctionInvocation(rec1.typed, List(x)))

  private val classA = new CaseClassDef(FreshIdentifier("A"), Seq(), None, false)
  private val classAField = FreshIdentifier("x", IntegerType)
  classA.setFields(Seq(ValDef(classAField).setIsVar(true)))
  private val classAInstanceId = FreshIdentifier("a", classA.typed)
  private val classAInstance = classAInstanceId.toVariable


  test("expression with no variable has no alias") {
    val aliasAnalysis = new AliasAnalysis
    assert(aliasAnalysis.expressionAliasing(bi(42)) === Set())
    assert(aliasAnalysis.expressionAliasing(i(1)) === Set())
    assert(aliasAnalysis.expressionAliasing(BooleanLiteral(true)) === Set())
  }

  test("Lets in expression are aliases") {
    val aliasAnalysis = new AliasAnalysis
    assert(aliasAnalysis.expressionAliasing(Let(x.id, y, x)) === Set(x.id, y.id))
    assert(aliasAnalysis.expressionAliasing(Let(x.id, y, y)) === Set(x.id, y.id))
    assert(aliasAnalysis.expressionAliasing(Let(x.id, bi(12), x)) === Set(x.id))
    assert(aliasAnalysis.expressionAliasing(Let(x.id, bi(12), Let(y.id, x, y))) === Set(x.id, y.id))
    assert(aliasAnalysis.expressionAliasing(Let(x.id, bi(12), Let(y.id, x, x))) === Set(x.id, y.id))

    assert(aliasAnalysis.expressionAliasing(Let(x.id, y, Let(z.id, x, z))) === Set(x.id, y.id, z.id))
    assert(aliasAnalysis.expressionAliasing(Let(x.id, y, Let(z.id, x, y))) === Set(x.id, y.id, z.id))
  }

  test("Lets that are not returned are not aliases") {
    val aliasAnalysis = new AliasAnalysis
    assert(aliasAnalysis.expressionAliasing(Let(x.id, bi(12), bi(10))) === Set())
    assert(aliasAnalysis.expressionAliasing(Let(x.id, bi(12), y)) === Set(y.id))
    assert(aliasAnalysis.expressionAliasing(Let(x.id, y, Let(z.id, bi(12), x))) === Set(x.id, y.id))
    assert(aliasAnalysis.expressionAliasing(Let(x.id, y, Let(z.id, bi(12), y))) === Set(x.id, y.id))
  }
}
