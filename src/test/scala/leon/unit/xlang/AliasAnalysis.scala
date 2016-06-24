/* Copyright 2009-2016 EPFL, Lausanne */

package leon.unit.xlang

import org.scalatest._

import leon.test._
import leon.purescala.Common._
import leon.purescala.Expressions._
import leon.purescala.Types._
import leon.purescala.TypeOps.isSubtypeOf
import leon.purescala.Definitions._
import leon.xlang.{AliasAnalysis, LeonAliasAnalysis}
import leon.xlang.Expressions._
import leon.xlang.ExprOps._

class AliasAnalysisSuite extends FunSuite with helpers.ExpressionsDSL {
  private val classA = new CaseClassDef(FreshIdentifier("A"), Seq(), None, false)
  private val classAField = FreshIdentifier("x", IntegerType)
  classA.setFields(Seq(ValDef(classAField)))
  private val classAInstance1Id = FreshIdentifier("a1", classA.typed)
  private val classAInstance1 = classAInstance1Id.toVariable
  private val classAInstance2Id = FreshIdentifier("a2", classA.typed)
  private val classAInstance2 = classAInstance2Id.toVariable
  private val classAInstance3Id = FreshIdentifier("a3", classA.typed)
  private val classAInstance3 = classAInstance3Id.toVariable

  private val classB = new CaseClassDef(FreshIdentifier("B"), Seq(), None, false)
  private val classBField = FreshIdentifier("a", classA.typed)
  classB.setFields(Seq(ValDef(classBField)))
  private val classBInstance1Id = FreshIdentifier("b1", classB.typed)
  private val classBInstance1 = classBInstance1Id.toVariable


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

  test("asInstanceOf does not remove aliasing") {
    val aliasAnalysis = new AliasAnalysis
    assert(aliasAnalysis.expressionAliasing(AsInstanceOf(classAInstance1, classA.typed)) === Set(classAInstance1Id))
    assert(aliasAnalysis.expressionAliasing(AsInstanceOf(AsInstanceOf(classAInstance1, classA.typed), classA.typed)) === Set(classAInstance1Id))
    assert(aliasAnalysis.expressionAliasing(Let(classAInstance2Id, AsInstanceOf(classAInstance1, classA.typed), AsInstanceOf(classAInstance2, classA.typed))) === Set(classAInstance1Id, classAInstance2Id))
  }

  test("IfExpr can alias with both branches") {
    val aliasAnalysis = new AliasAnalysis
    assert(aliasAnalysis.expressionAliasing(IfExpr(BooleanLiteral(true), x, y)) === Set(x.id, y.id))
    assert(aliasAnalysis.expressionAliasing(IfExpr(BooleanLiteral(true), x, bi(13))) === Set(x.id))
  }

  test("Pattern matching introduce aliases") {
    val aliasAnalysis = new AliasAnalysis
    val m1 = MatchExpr(x, Seq(MatchCase(WildcardPattern(Some(y.id)), None, y)))
    assert(aliasAnalysis.expressionAliasing(m1) === Set(x.id, y.id))
    val m2 = MatchExpr(x, Seq(MatchCase(WildcardPattern(Some(y.id)), None, x)))
    assert(aliasAnalysis.expressionAliasing(m2) === Set(x.id, y.id))
    val m3 = MatchExpr(x, Seq(MatchCase(WildcardPattern(Some(y.id)), None, bi(12))))
    assert(aliasAnalysis.expressionAliasing(m3) === Set())

    //TODO: we probably need to distinguish aliases per type, and not keep the abstraction all aliases to some part of an object graph
    val m4 = MatchExpr(classAInstance1, Seq(MatchCase(CaseClassPattern(None, classA.typed, Seq(WildcardPattern(Some(y.id)))), None, y)))
    assert(aliasAnalysis.expressionAliasing(m4) === Set(y.id, classAInstance1Id))
    val m5 = MatchExpr(classAInstance1, Seq(MatchCase(CaseClassPattern(Some(classAInstance2Id), classA.typed, Seq(WildcardPattern(Some(x.id)))), None, x)))
    assert(aliasAnalysis.expressionAliasing(m5) === Set(x.id, classAInstance1Id, classAInstance2Id))

    val m6 = MatchExpr(classAInstance1, Seq(
      MatchCase(CaseClassPattern(Some(classAInstance2Id), classA.typed, Seq(WildcardPattern(Some(x.id)))), None, x),
      MatchCase(CaseClassPattern(Some(classAInstance3Id), classA.typed, Seq(WildcardPattern(Some(y.id)))), None, y)
    ))
    assert(aliasAnalysis.expressionAliasing(m6) === Set(x.id, y.id, classAInstance1Id, classAInstance2Id, classAInstance3Id))
  }

  test("expression to field of class aliases to root class") {
    val aliasAnalysis = new AliasAnalysis
    assert(aliasAnalysis.expressionAliasing(CaseClassSelector(classB.typed, classBInstance1, classBField)) === Set(classBInstance1Id))
    assert(aliasAnalysis.expressionAliasing(Let(classAInstance1Id, CaseClassSelector(classB.typed, classBInstance1, classBField), classAInstance1)) === Set(classAInstance1Id, classBInstance1Id))
  }

  test("Block can return alias in last expressions") {
    val aliasAnalysis = new AliasAnalysis
    assert(aliasAnalysis.expressionAliasing(Block(Seq(), x)) === Set(x.id))
  }
  test("Only last expression of a block is an alias") {
    val aliasAnalysis = new AliasAnalysis
    assert(aliasAnalysis.expressionAliasing(Block(Seq(y), x)) === Set(x.id))
  }
  test("Assignments in blocks can modify aliasing in the end") {
    val aliasAnalysis = new AliasAnalysis
    assert(aliasAnalysis.expressionAliasing(Block(Seq(Assignment(y.id, x)), x)) === Set(x.id, y.id))
  }

  test("Assignment burried in expressions should still be taken into account for aliasing") {
    val aliasAnalysis = new AliasAnalysis
    assert(aliasAnalysis.expressionAliasing(Let(x.id, Plus(bi(10), Block(Seq(Assignment(y.id, z)), bi(12))), y)) === Set(y.id, z.id))
  }


  private val fd1 = new FunDef(FreshIdentifier("f1"), Seq(), Seq(ValDef(x.id)), IntegerType)
  fd1.body = Some(x)

  private val fd2 = new FunDef(FreshIdentifier("f2"), Seq(), Seq(ValDef(y.id)), IntegerType)
  fd2.body = Some(FunctionInvocation(fd1.typed, List(y)))

  private val rec1 = new FunDef(FreshIdentifier("rec1"), Seq(), Seq(ValDef(x.id)), IntegerType)
  rec1.body = Some(FunctionInvocation(rec1.typed, List(x)))

  test("simple function aliases its returned value") {
    val aliasAnalysis = new AliasAnalysis
    assert(aliasAnalysis.functionAliasing(fd1) === Set(x.id))
  }
  test("simple function that returns literal has no aliases") {
    val fd = new FunDef(FreshIdentifier("fd"), Seq(), Seq(ValDef(x.id)), IntegerType)
    fd.body = Some(bi(42))
    val aliasAnalysis = new AliasAnalysis
    assert(aliasAnalysis.functionAliasing(fd) === Set())
  }
  test("function aliases with transitive call") {
    val aliasAnalysis = new AliasAnalysis
    assert(aliasAnalysis.functionAliasing(fd2) === Set(y.id))
  }
  test("function that calls an aliased function with a literal should not alias") {
    val fd = new FunDef(FreshIdentifier("fd"), Seq(), Seq(ValDef(x.id)), IntegerType)
    fd.body = Some(FunctionInvocation(fd.typed, List(bi(42))))
    val aliasAnalysis = new AliasAnalysis
    assert(aliasAnalysis.functionAliasing(fd) === Set())
  }
  test("Alias analysis state is consistent") {
    //basically, we check that mutliple calls are fine
    val aliasAnalysis = new AliasAnalysis
    assert(aliasAnalysis.functionAliasing(fd1) === Set(x.id))
    assert(aliasAnalysis.functionAliasing(fd1) === Set(x.id))
    assert(aliasAnalysis.functionAliasing(fd2) === Set(y.id))
    assert(aliasAnalysis.functionAliasing(fd2) === Set(y.id))
    assert(aliasAnalysis.functionAliasing(fd1) === Set(x.id))

    val fd = new FunDef(FreshIdentifier("fd"), Seq(), Seq(ValDef(x.id)), IntegerType)
    fd.body = Some(bi(42))
    assert(aliasAnalysis.functionAliasing(fd) === Set())
    assert(aliasAnalysis.functionAliasing(fd1) === Set(x.id))
    assert(aliasAnalysis.functionAliasing(fd2) === Set(y.id))
  }
  test("function with internal aliases only return aliasing to its parameter") {
    val fd = new FunDef(FreshIdentifier("fd"), Seq(), Seq(ValDef(x.id)), IntegerType)
    fd.body = Some(Let(y.id, x, y))
    val aliasAnalysis = new AliasAnalysis
    assert(aliasAnalysis.functionAliasing(fd) === Set(x.id))
  }
  test("function with alias to external id returns it") {
    val aliasAnalysis = new AliasAnalysis

    val f1 = new FunDef(FreshIdentifier("f1"), Seq(), Seq(ValDef(x.id)), IntegerType)
    f1.body = Some(y)
    assert(aliasAnalysis.functionAliasing(f1) === Set(y.id))

    val f2 = new FunDef(FreshIdentifier("f2"), Seq(), Seq(ValDef(x.id)), IntegerType)
    f2.body = Some(Let(y.id, z, y))
    assert(aliasAnalysis.functionAliasing(f2) === Set(z.id))
  }
  test("function with assignment to external id returns correctly the alias") {
    val f1 = new FunDef(FreshIdentifier("f1"), Seq(), Seq(ValDef(x.id)), IntegerType)
    f1.body = Some(Block(Seq(Assignment(y.id, x)), x))
    val aliasAnalysis = new AliasAnalysis
    assert(aliasAnalysis.functionAliasing(f1) === Set(x.id, y.id))
  }


  test("invocation of a function with global aliasing should consider both argument and global value in aliasing") {
    val fd = new FunDef(FreshIdentifier("fd"), Seq(), Seq(ValDef(x.id)), IntegerType)
    fd.body = Some(Block(Seq(Assignment(y.id, x)), x)) //returned value aliases to param x and global y
    val aliasAnalysis = new AliasAnalysis
    assert(aliasAnalysis.expressionAliasing(FunctionInvocation(fd.typed, Seq(z))) === Set(z.id, y.id))
  }


  val hof = FreshIdentifier("f", FunctionType(Seq(IntegerType), IntegerType)).toVariable
  val fd3 = new FunDef(FreshIdentifier("f3"), Seq(), Seq(ValDef(x.id), ValDef(hof.id)), IntegerType)
  fd3.body = Some(Application(hof, Seq(x)))

  test("higher order function could alias any parameters") {
    val aliasAnalysis = new AliasAnalysis
    assert(aliasAnalysis.functionAliasing(fd3) === Set(x.id))
  }
  test("higher order function does not alias with leon alias analysis") {
    val aliasAnalysis = new LeonAliasAnalysis
    assert(aliasAnalysis.functionAliasing(fd3) === Set())
  }
}
