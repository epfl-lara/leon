/* Copyright 2009-2016 EPFL, Lausanne */

package leon.integration.evaluators

import leon.test._
import helpers.ExpressionsDSLProgram
import leon.evaluators._
import leon.purescala.Definitions._
import leon.purescala.Expressions._
import leon.purescala.Types._
import org.scalatest.Matchers

class AbstractEvaluatorSuite  extends LeonTestSuiteWithProgram with ExpressionsDSLProgram with Matchers {
  //override def a = super[ExpressionsDSL].a
  
  val sources = List("""
import leon.lang._

object AbstractTests {
  abstract class Tree
  case class Node(w: Tree, x: Int, y: Tree) extends Tree
  case class Leaf() extends Tree

  def param(x: String) = x + x
 
  def test() = {
    val x = "19"
    val w = 9
    val y = () => w*w+5
    val z = y().toString
    val res = param(x) + z
    res
  }
  
  def test2(right: Boolean, c: Tree): Int = {
    if(right) {
      c match {
        case Leaf() => 0
        case Node(_, a, Leaf()) => a
        case Node(_, _, n) => test2(right, n)
      }
    } else {
      c match {
        case Leaf() => 0
        case Node(Leaf(), a, _) => a
        case Node(n, _, _) => test2(right, n)
      }
    }
  }
}""")
  
  test("Abstract evaluator should keep track of variables") { implicit fix =>
    val testFd = funDef("AbstractTests.test")

    val ae = new AbstractEvaluator(fix._1, fix._2)
    
    val res = ae.eval(FunctionInvocation(testFd.typed, Seq()))
    
    res.result match {
      case Some((e, expr)) =>
        e should equal (StringLiteral("191986"))
        expr should equal (StringConcat(StringConcat(StringLiteral("19"), StringLiteral("19")), Int32ToString(BVPlus(BVTimes(IntLiteral(9), IntLiteral(9)), IntLiteral(5)))))
      case None =>
        fail("No result!")
    }
  }
  
  
  test("AbstractOnly evaluator should keep track of variables") { implicit fix =>
    val testFd = funDef("AbstractTests.test")

    val aeOnly = new AbstractOnlyEvaluator(fix._1, fix._2)
    
    val res2 = aeOnly.eval(FunctionInvocation(testFd.typed, Seq()))
    
    res2.result match {
      case Some(expr) =>
        expr should equal (StringConcat(StringConcat(StringLiteral("19"), StringLiteral("19")), Int32ToString(BVPlus(BVTimes(IntLiteral(9), IntLiteral(9)), IntLiteral(5)))))
      case None =>
        fail("No result!")
    }
  }
  
  test("Abstract evaluator should correctly handle boolean and recursive") { implicit fix =>
    val testFd = funDef("AbstractTests.test2")
    val Leaf = cc("AbstractTests.Leaf")()
    def Node(left: Expr, n: Expr, right: Expr) = cc("AbstractTests.Node")(left, n, right)
    val NodeDef = classDef("AbstractTests.Node")
    val NodeType = classType("AbstractTests.Node", Seq()).asInstanceOf[CaseClassType]
    
    val ae = new AbstractEvaluator(fix._1, fix._2)
    ae.evaluateCaseClassSelector = false
    
    val input = Node(Leaf, IntLiteral(5), Leaf)
    
    val res = ae.eval(FunctionInvocation(testFd.typed, Seq(BooleanLiteral(true), input))).result match {
      case Some((e, expr)) =>
        e should equal (IntLiteral(5))
        expr should equal (CaseClassSelector(NodeType, input, NodeDef.fieldsIds(1)))
      case None =>
        fail("No result!")
    }
    val a = id("a", Int32Type)
    val input2 = Node(Leaf, Variable(a), Leaf)
    ae.eval(FunctionInvocation(testFd.typed, Seq(BooleanLiteral(true), input2))).result match {
      case Some((e, expr)) =>
        e should equal (Variable(a))
        expr should equal (CaseClassSelector(NodeType, input2, NodeDef.fieldsIds(1)))
      case None =>
        fail("No result!")
    }
  }
}
