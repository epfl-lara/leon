/* Copyright 2009-2013 EPFL, Lausanne */

package leon.test
package purescala

import leon._
import leon.plugin.{TemporaryInputPhase,ExtractionPhase}

import leon.purescala.Common._
import leon.purescala.Trees._
import leon.purescala.Definitions._
import leon.purescala.TypeTrees._
import leon.datagen._

import leon.evaluators._

import org.scalatest.FunSuite

class DataGen extends FunSuite {
  private implicit lazy val leonContext = LeonContext(
    settings = Settings(
      synthesis = false,
      xlang     = false,
      verify    = false
    ),
    files = List(),
    reporter = new SilentReporter
  )

  private def parseString(str : String) : Program = {
    val pipeline = TemporaryInputPhase andThen ExtractionPhase

    val errorsBefore   = leonContext.reporter.errorCount
    val warningsBefore = leonContext.reporter.warningCount

    val program = pipeline.run(leonContext)((str, Nil))
  
    assert(leonContext.reporter.errorCount   === errorsBefore)
    assert(leonContext.reporter.warningCount === warningsBefore)

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

    val eval      = new DefaultEvaluator(leonContext, prog)
    val generator = new NaiveDataGen(leonContext, prog, eval)

    generator.generate(BooleanType).toSet.size === 2
    generator.generate(TupleType(Seq(BooleanType,BooleanType))).toSet.size === 4

    val listType : TypeTree = classDefToClassType(prog.mainObject.classHierarchyRoots.head)
    val sizeDef    : FunDef = prog.definedFunctions.find(_.id.name == "size").get
    val sortedDef  : FunDef = prog.definedFunctions.find(_.id.name == "isSorted").get
    val contentDef : FunDef = prog.definedFunctions.find(_.id.name == "content").get
    val insSpecDef : FunDef = prog.definedFunctions.find(_.id.name == "insertSpec").get

    val consDef : CaseClassDef = prog.mainObject.caseClassDef("Cons")

    generator.generate(listType).take(100).toSet.size === 100

    val evaluator = new CodeGenEvaluator(leonContext, prog)

    val a = Variable(FreshIdentifier("a").setType(Int32Type))
    val b = Variable(FreshIdentifier("b").setType(Int32Type))
    val x = Variable(FreshIdentifier("x").setType(listType))
    val y = Variable(FreshIdentifier("y").setType(listType))

    val sizeX    = FunctionInvocation(sizeDef, Seq(x))
    val contentX = FunctionInvocation(contentDef, Seq(x))
    val contentY = FunctionInvocation(contentDef, Seq(y))
    val sortedX  = FunctionInvocation(sortedDef, Seq(x))
    val sortedY  = FunctionInvocation(sortedDef, Seq(y))

    assert(generator.generateFor(
      Seq(x.id),
      GreaterThan(sizeX, IntLiteral(0)),
      10,
      500
    ).size === 10)

    assert(generator.generateFor(
      Seq(x.id, y.id),
      And(Equals(contentX, contentY), sortedY),
      10,
      500
    ).size === 10)

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
        FunctionInvocation(sortedDef, Seq(CaseClass(consDef, Seq(a, x)))),
        FunctionInvocation(insSpecDef, Seq(b, x, y))
      )),
      10,
      500
    ).size >= 5, "There should be at least 5 models for this problem.")
  }
}
