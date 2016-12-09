/* Copyright 2009-2016 EPFL, Lausanne */

package leon.unit.xlang

import org.scalatest._

import leon.test._
import leon.purescala.Common._
import leon.purescala.Expressions._
import leon.purescala.Types._
import leon.purescala.TypeOps.isSubtypeOf
import leon.purescala.Definitions._
import leon.xlang.EffectsAnalysis
import leon.xlang.Expressions._
import leon.xlang.ExprOps._

class EffectsAnalysisSuite extends FunSuite with helpers.ExpressionsDSL {

  private val fd1 = new FunDef(FreshIdentifier("f1"), Seq(), Seq(ValDef(x.id)), IntegerType)
  fd1.body = Some(x)

  private val fd2 = new FunDef(FreshIdentifier("f2"), Seq(), Seq(ValDef(x.id)), IntegerType)
  fd2.body = Some(FunctionInvocation(fd1.typed, List(bi(1))))

  private val rec1 = new FunDef(FreshIdentifier("rec1"), Seq(), Seq(ValDef(x.id)), IntegerType)
  rec1.body = Some(FunctionInvocation(rec1.typed, List(x)))

  test("Pure functions have no effects") {
    val effects = new EffectsAnalysis
    assert(effects(fd1) === Set())
    assert(effects(fd2) === Set())
    assert(effects(rec1) === Set())
  }


  private val classA = new CaseClassDef(FreshIdentifier("A"), Seq(), None, false)
  private val classAField = FreshIdentifier("x", IntegerType)
  classA.setFields(Seq(ValDef(classAField).setIsVar(true)))
  private val classAInstanceId = FreshIdentifier("a", classA.typed)
  private val classAInstance = classAInstanceId.toVariable

  private val mfd1 = new FunDef(FreshIdentifier("mf1"), Seq(), Seq(ValDef(classAInstanceId)), UnitType)
  mfd1.body = Some(FieldAssignment(classAInstance, classAField, bi(15)))

  test("Simple function that mutates its param has an effect") {
    val effects = new EffectsAnalysis
    assert(effects(mfd1) === Set(0))
    assert(effects(fd1) === Set())
  }

  test("Function that with immutable param has right effect") {
    val fd = new FunDef(FreshIdentifier("f"), Seq(), Seq(ValDef(x.id), ValDef(classAInstanceId)), UnitType)
    fd.body = Some(FieldAssignment(classAInstance, classAField, bi(15)))

    val effects = new EffectsAnalysis
    assert(effects(fd) === Set(1))
  }

  test("Function that takes a mutable param but does not mutate it has no effect") {
    val fd = new FunDef(FreshIdentifier("f"), Seq(), Seq(ValDef(classAInstanceId)), UnitType)
    fd.body = Some(UnitLiteral())

    val effects = new EffectsAnalysis
    assert(effects(fd) === Set())
  }


  test("Function that mutates param via transitive call has effects") {
    val fd = new FunDef(FreshIdentifier("f"), Seq(), Seq(ValDef(classAInstanceId)), UnitType)
    fd.body = Some(FunctionInvocation(mfd1.typed, Seq(classAInstance)))

    val effects = new EffectsAnalysis
    assert(effects(fd) === Set(0))
    assert(effects(mfd1) === Set(0))
    assert(effects(fd1) === Set())
  }
  test("Function that mutates param via multiple transitive call has effects") {
    val fd = new FunDef(FreshIdentifier("f"), Seq(), Seq(ValDef(classAInstanceId)), UnitType)
    fd.body = Some(FunctionInvocation(mfd1.typed, Seq(classAInstance)))
    val nfd = new FunDef(FreshIdentifier("f"), Seq(), Seq(ValDef(classAInstanceId)), UnitType)
    nfd.body = Some(FunctionInvocation(fd.typed, Seq(classAInstance)))

    val effects = new EffectsAnalysis
    assert(effects(nfd) === Set(0))
    assert(effects(fd) === Set(0))
    assert(effects(mfd1) === Set(0))
  }

  private val classB = new CaseClassDef(FreshIdentifier("B"), Seq(), None, false)
  private val classBField = FreshIdentifier("y", IntegerType)
  classB.setFields(Seq(ValDef(classBField).setIsVar(true)))
  private val classBInstanceId = FreshIdentifier("b", classB.typed)
  private val classBInstance = classBInstanceId.toVariable

  test("Function that with mutate only one param detects right effect") {
    val fd = new FunDef(FreshIdentifier("f"), Seq(), Seq(ValDef(classBInstanceId), ValDef(classAInstanceId)), UnitType)
    fd.body = Some(FieldAssignment(classAInstance, classAField, bi(15)))

    val effects = new EffectsAnalysis
    assert(effects(fd) === Set(1))
  }

  test("Mutually recursives functions without effects are pure") {
    val rfd1 = new FunDef(FreshIdentifier("rf1"), Seq(), Seq(ValDef(classAInstanceId), ValDef(classBInstanceId)), UnitType)
    val rfd2 = new FunDef(FreshIdentifier("rf2"), Seq(), Seq(ValDef(classAInstanceId), ValDef(classBInstanceId)), UnitType)
    rfd1.body = Some(FunctionInvocation(rfd2.typed, Seq(classAInstance, classBInstance)))
    rfd2.body = Some(FunctionInvocation(rfd1.typed, Seq(classAInstance, classBInstance)))

    val effects = new EffectsAnalysis
    assert(effects(rfd1) === Set())
    assert(effects(rfd2) === Set())
  }

  test("Mutually recursives functions with effects are transitively detected") {
    val rfd1 = new FunDef(FreshIdentifier("rf1"), Seq(), Seq(ValDef(classAInstanceId), ValDef(classBInstanceId)), UnitType)
    val rfd2 = new FunDef(FreshIdentifier("rf2"), Seq(), Seq(ValDef(classAInstanceId), ValDef(classBInstanceId)), UnitType)
    rfd1.body = Some(Block(Seq(FieldAssignment(classAInstance, classAField, bi(10))), FunctionInvocation(rfd2.typed, Seq(classAInstance, classBInstance))))
    rfd2.body = Some(FunctionInvocation(rfd1.typed, Seq(classAInstance, classBInstance)))

    val effects = new EffectsAnalysis
    assert(effects(rfd1) === Set(0))
    assert(effects(rfd2) === Set(0))
  }

  test("Mutually recursives functions with multiple effects are transitively detected") {
    val rfd1 = new FunDef(FreshIdentifier("rf1"), Seq(), Seq(ValDef(classAInstanceId), ValDef(classBInstanceId)), UnitType)
    val rfd2 = new FunDef(FreshIdentifier("rf2"), Seq(), Seq(ValDef(classAInstanceId), ValDef(classBInstanceId)), UnitType)
    rfd1.body = Some(Block(Seq(FieldAssignment(classAInstance, classAField, bi(10))), FunctionInvocation(rfd2.typed, Seq(classAInstance, classBInstance))))
    rfd2.body = Some(Block(Seq(FieldAssignment(classBInstance, classBField, bi(12))), FunctionInvocation(rfd1.typed, Seq(classAInstance, classBInstance))))

    val effects = new EffectsAnalysis
    assert(effects(rfd1) === Set(0,1))
    assert(effects(rfd2) === Set(0,1))
  }


  private val lambdaId = FreshIdentifier("lambda", FunctionType(Seq(classA.typed), UnitType))
  private val mfd2 = new FunDef(FreshIdentifier("mf2"), Seq(), Seq(ValDef(classAInstanceId), ValDef(lambdaId)), UnitType)
  mfd2.body = Some(Application(lambdaId.toVariable, Seq(classAInstance)))


  test("Function that takes higher-order function applied to a mutable param has effects") {
    val effects = new EffectsAnalysis
    assert(effects(mfd2) === Set(0))
  }


  test("Assignment has effect on local variable being assigned") {
    val effects = new EffectsAnalysis
    assert(effects(Assignment(x.id, bi(42))) === Set(x.id))
    assert(effects(Assignment(x.id, y)) === Set(x.id))
  }
  test("Assignment has no effect if variable isn't free") {
    val x = FreshIdentifier("x", IntegerType)
    val effects = new EffectsAnalysis
    assert(effects(LetVar(x, bi(10), Assignment(x, bi(42)))) === Set())
  }
  test("Block can have multiple effects") {
    val effects = new EffectsAnalysis
    assert(effects(Block(Seq(Assignment(x.id, bi(42))), Assignment(y.id, bi(12)))) === Set(x.id, y.id))
  }

  //TODO: should test that a fun def can have effects on local captured variables
}
