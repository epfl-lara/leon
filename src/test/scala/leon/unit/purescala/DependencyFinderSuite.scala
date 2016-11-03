/* Copyright 2009-2016 EPFL, Lausanne */

package leon.unit.purescala

import org.scalatest._

import leon.test._
import leon.purescala.Common._
import leon.purescala.Expressions._
import leon.purescala.Types._
import leon.purescala.Definitions._
import leon.purescala.DependencyFinder

class DependencyFinderSuite extends FunSuite with helpers.ExpressionsDSL {

  private val fd1 = new FunDef(FreshIdentifier("f1"), Seq(), Seq(ValDef(x.id)), IntegerType)
  fd1.body = Some(x)

  private val fd2 = new FunDef(FreshIdentifier("f2"), Seq(), Seq(ValDef(x.id)), IntegerType)
  fd2.body = Some(FunctionInvocation(fd1.typed, List(bi(1))))

  private val rec1 = new FunDef(FreshIdentifier("rec1"), Seq(), Seq(ValDef(x.id)), IntegerType)
  rec1.body = Some(FunctionInvocation(rec1.typed, List(x)))

  test("Direct fun def dependencies with function invocation in body") {
    val deps = new DependencyFinder
    assert(deps(fd1) === Set())
    assert(deps(fd2) === Set(fd1))
    assert(deps(rec1) === Set(rec1))
  }

  test("transitive fun def dependencies with function invocation in body") {
    val fd = new FunDef(FreshIdentifier("f"), Seq(), Seq(ValDef(x.id)), IntegerType)
    fd.body = Some(FunctionInvocation(fd2.typed, List(bi(1))))
    val deps = new DependencyFinder
    assert(deps(fd) === Set(fd1, fd2))
    assert(deps(fd1) === Set())
    assert(deps(fd2) === Set(fd1))
  }

  private val classA = new CaseClassDef(FreshIdentifier("A"), Seq(), None, false)
  private val classAField = FreshIdentifier("x", IntegerType)
  classA.setFields(Seq(ValDef(classAField)))
  private val classB = new CaseClassDef(FreshIdentifier("B"), Seq(), None, false)
  private val classBField = FreshIdentifier("a", classA.typed)
  classB.setFields(Seq(ValDef(classBField)))

  test("Direct class def dependencies via fields") {
    val deps = new DependencyFinder
    assert(deps(classB) === Set(classA))
  }

  test("Direct fun def dependencies with case class selectors in body") {
    val a = FreshIdentifier("a", classA.typed)
    val fd = new FunDef(FreshIdentifier("f"), Seq(), Seq(ValDef(a)), classAField.getType)
    fd.body = Some(CaseClassSelector(classA.typed, a.toVariable, classAField))
    val deps = new DependencyFinder
    assert(deps(fd) === Set(classA))
  }

  test("Transitive fun def dependencies with case class selectors in body") {
    val b = FreshIdentifier("b", classB.typed)
    val fd = new FunDef(FreshIdentifier("f"), Seq(), Seq(ValDef(b)), classBField.getType)
    fd.body = Some(CaseClassSelector(classB.typed, b.toVariable, classBField))
    val deps = new DependencyFinder
    assert(deps(fd) === Set(classB, classA))
  }


  test("Class depends on its invariant") {
    val classC = new CaseClassDef(FreshIdentifier("C"), Seq(), None, false)
    val classCField = FreshIdentifier("x", IntegerType)
    classC.setFields(Seq(ValDef(classCField)))

    val thisId = FreshIdentifier("this", classC.typed)

    val inv = new FunDef(FreshIdentifier("inv"), Seq(), Seq(ValDef(thisId)), BooleanType)
    inv.body = Some(BooleanLiteral(true))
    classC.setInvariant(inv)

    val deps = new DependencyFinder
    assert(deps(classC) === Set(inv, classC))
  }

  test("Class depends on invariant of its dependencies") {
    val classC = new CaseClassDef(FreshIdentifier("C"), Seq(), None, false)
    val classCField = FreshIdentifier("x", IntegerType)
    classC.setFields(Seq(ValDef(classCField)))
    val classD = new CaseClassDef(FreshIdentifier("D"), Seq(), None, false)
    val classDField = FreshIdentifier("c", classC.typed)
    classD.setFields(Seq(ValDef(classDField)))

    val thisId = FreshIdentifier("this", classC.typed)

    val inv = new FunDef(FreshIdentifier("inv"), Seq(), Seq(ValDef(thisId)), BooleanType)
    inv.body = Some(BooleanLiteral(true))
    classC.setInvariant(inv)

    val deps = new DependencyFinder
    assert(deps(classD) === Set(inv, classC))
    assert(deps(classC) === Set(inv, classC))
  }

  test("Class depends on invariant and transitive deps") {
    val classC = new CaseClassDef(FreshIdentifier("C"), Seq(), None, false)
    val classCField = FreshIdentifier("x", IntegerType)
    classC.setFields(Seq(ValDef(classCField)))
    val classD = new CaseClassDef(FreshIdentifier("D"), Seq(), None, false)
    val classDField = FreshIdentifier("c", classC.typed)
    classD.setFields(Seq(ValDef(classDField)))

    val thisId = FreshIdentifier("this", classC.typed)

    val inv = new FunDef(FreshIdentifier("inv"), Seq(), Seq(ValDef(thisId)), BooleanType)
    inv.body = Some(FunctionInvocation(fd2.typed, Seq(bi(10))))
    classC.setInvariant(inv)

    val deps = new DependencyFinder
    assert(deps(classD) === Set(inv, classC, fd2, fd1))
  }

  test("Dependencies of mutually recursive functions") {
    val rec1 = new FunDef(FreshIdentifier("rec1"), Seq(), Seq(ValDef(x.id)), IntegerType)
    val rec2 = new FunDef(FreshIdentifier("rec2"), Seq(), Seq(ValDef(x.id)), IntegerType)
    rec1.body = Some(FunctionInvocation(rec2.typed, List(bi(1))))
    rec2.body = Some(FunctionInvocation(rec1.typed, List(bi(1))))

    val deps = new DependencyFinder
    assert(deps(rec1) === Set(rec1, rec2))
    assert(deps(rec2) === Set(rec1, rec2))
  }

  test("Finding all transitive dependencies of a function invocation expression") {
    val deps = new DependencyFinder
    assert(deps(FunctionInvocation(fd2.typed, Seq(bi(12)))) === Set(fd1, fd2))
  }
}
