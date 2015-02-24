/* Copyright 2009-2014 EPFL, Lausanne */

package leon.test.purescala

import leon._
import leon.test._
import leon.utils.{TemporaryInputPhase, PreprocessingPhase}
import leon.frontends.scalac.ExtractionPhase

import leon.purescala.Common._
import leon.purescala.Trees._
import leon.purescala.Definitions._
import leon.purescala.TypeTrees._
import leon.datagen._

import leon.evaluators._

import org.scalatest.FunSuite

class DataGen extends LeonTestSuite {
  private def parseString(str : String) : Program = {
    val pipeline = TemporaryInputPhase andThen ExtractionPhase andThen PreprocessingPhase

    val errorsBefore   = testContext.reporter.errorCount
    val warningsBefore = testContext.reporter.warningCount

    val program = pipeline.run(testContext)((str, Nil))
  
    assert(testContext.reporter.errorCount   === errorsBefore)
    assert(testContext.reporter.warningCount === warningsBefore)

    program
  }

  test("Lists") {
    val p = """|object Program {
               |  sealed abstract class List
               |  case class Cons(head : Int, tail : List) extends List
               |  case object Nil extends List
               |
               |  def size(lst : List) : Int = lst match {
               |    case Cons(_, xs) => 1 + size(xs)
               |    case Nil => 0
               |  }
               |
               |  def isSorted(lst : List) : Boolean = lst match {
               |    case Nil => true
               |    case Cons(_, Nil) => true
               |    case Cons(x, xs @ Cons(y, ys)) => x < y && isSorted(xs)
               |  }
               |
               |  def content(lst : List) : Set[Int] = lst match {
               |    case Nil => Set.empty[Int]
               |    case Cons(x, xs) => Set(x) ++ content(xs)
               |  }
               |
               |  def insertSpec(elem : Int, list : List, res : List) : Boolean = {
               |    isSorted(res) && content(res) == (content(list) ++ Set(elem))
               |  }
               |}""".stripMargin

    val prog = parseString(p)

    val eval      = new DefaultEvaluator(testContext, prog)
    val generator = new NaiveDataGen(testContext, prog, eval)

    generator.generate(BooleanType).toSet.size === 2
    generator.generate(TupleType(Seq(BooleanType,BooleanType))).toSet.size === 4

    // Make sure we target our own lists
    val module = prog.units.flatMap{_.modules}.find(_.id.name == "Program").get
    val listType : TypeTree = classDefToClassType(module.classHierarchyRoots.head)
    val sizeDef    : FunDef = module.definedFunctions.find(_.id.name == "size").get
    val sortedDef  : FunDef = module.definedFunctions.find(_.id.name == "isSorted").get
    val contentDef : FunDef = module.definedFunctions.find(_.id.name == "content").get
    val insSpecDef : FunDef = module.definedFunctions.find(_.id.name == "insertSpec").get

    val consDef : CaseClassDef = module.definedClasses.collect {
      case ccd: CaseClassDef if ccd.id.name == "Cons" => ccd
    }.head

    assert(generator.generate(listType).take(100).toSet.size === 100, "Should be able to generate 100 different lists")

    val evaluator = new CodeGenEvaluator(testContext, prog)

    val a = Variable(FreshIdentifier("a", Int32Type))
    val b = Variable(FreshIdentifier("b", Int32Type))
    val x = Variable(FreshIdentifier("x", listType))
    val y = Variable(FreshIdentifier("y", listType))

    val sizeX    = FunctionInvocation(sizeDef.typed, Seq(x))
    val contentX = FunctionInvocation(contentDef.typed, Seq(x))
    val contentY = FunctionInvocation(contentDef.typed, Seq(y))
    val sortedX  = FunctionInvocation(sortedDef.typed, Seq(x))
    val sortedY  = FunctionInvocation(sortedDef.typed, Seq(y))

    assert(generator.generateFor(
      Seq(x.id),
      GreaterThan(sizeX, IntLiteral(0)),
      10,
      500
    ).size === 10, "Should find 10 non-empty lists in the first 500 enumerated")

    assert(generator.generateFor(
      Seq(x.id, y.id),
      And(Equals(contentX, contentY), sortedY),
      10,
      500
    ).size === 10, "Should find 2x 10 lists with same content in the first 500 enumerated")

    assert(generator.generateFor(
      Seq(x.id, y.id),
      And(Seq(Equals(contentX, contentY), sortedX, sortedY, Not(Equals(x, y)))),
      1,
      500
    ).isEmpty, "There should be no models for this problem")

    assert(generator.generateFor(
      Seq(x.id, y.id, b.id, a.id),
      And(Seq(
        LessThan(a, b),
        FunctionInvocation(sortedDef.typed, Seq(CaseClass(CaseClassType(consDef, Nil), Seq(a, x)))),
        FunctionInvocation(insSpecDef.typed, Seq(b, x, y))
      )),
      10,
      500
    ).size >= 5, "There should be at least 5 models for this problem.")
  }
}
