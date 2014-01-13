/* Copyright 2009-2013 EPFL, Lausanne */

package leon.test
package solvers.z3

import leon.purescala.Common._
import leon.purescala.Definitions._
import leon.purescala.Trees._
import leon.purescala.TreeOps._
import leon.purescala.TypeTrees._

import leon.solvers._
import leon.solvers.z3._

class FairZ3SolverGenericsTests extends LeonTestSuite {

  private val code =
    """
import leon.Utils._

object GenericStructures {
  abstract class List[T]
  case class Cons[T](head: T, tail: List[T]) extends List[T]
  case class Nil[T]() extends List[T]

  def size[T](list: List[T]): Int = list match {
    case Cons(head, tail) => 1 + size(tail)
    case Nil() => 0
  }
}
  """

  private val program = {
    val pipeline = leon.utils.TemporaryInputPhase andThen leon.frontends.scalac.ExtractionPhase
    pipeline.run(testContext)((code, Nil))
  }

  private val listClass = program.definedClasses.find(_.id.name == "List").get.asInstanceOf[AbstractClassDef]
  private val consClass = program.definedClasses.find(_.id.name == "Cons").get.asInstanceOf[CaseClassDef]
  private val nilClass = program.definedClasses.find(_.id.name == "Nil").get.asInstanceOf[CaseClassDef]
  private val size = program.definedFunctions.find(_.id.name == "size").get

  private val solver : SimpleSolverAPI = SimpleSolverAPI(FairZ3Solver.factory(testContext, program))

  private var testCounter : Int = 0
  private def solverCheck(expr : Expr, expected : Option[Boolean], msg : String) = {
    testCounter += 1

    test("Solver test #" + testCounter) {
      assert(solver.solveVALID(expr) === expected, msg)
    }
  }

  private def assertValid(expr : Expr) = solverCheck(
    expr, Some(true), "Solver should prove the formula " + expr + " valid."
  )

  private def assertInvalid(expr : Expr) = solverCheck(
    expr, Some(false), "Solver should prove the formula " + expr + " invalid."
  )

  private def assertUnknown(solver : SimpleSolverAPI, expr : Expr) = solverCheck(
    expr, None, "Solver should not be able to decide the formula " + expr + "."
  )

  private val booleanSize = {
    val nilType = CaseClassType(nilClass, Seq(BooleanType))
    val consType = CaseClassType(consClass, Seq(BooleanType))

    // build Cons(true, Cons(false, Cons(true, Nil())))
    val nil = CaseClass(nilType, Seq())
    val list1 = CaseClass(consType, Seq(BooleanLiteral(true), nil))
    val list2 = CaseClass(consType, Seq(BooleanLiteral(false), list1))
    val list3 = CaseClass(consType, Seq(BooleanLiteral(true), list2))

    Equals(FunctionInvocation(size, Seq(list3)), IntLiteral(3))
  }

  assertValid(booleanSize)
  
  private val intSize = {
    val nilType = CaseClassType(nilClass, Seq(Int32Type))
    val consType = CaseClassType(consClass, Seq(Int32Type))

    // build Cons(1, Cons(2, Cons(3, Nil())))
    val nil = CaseClass(nilType, Seq())
    val list1 = CaseClass(consType, Seq(IntLiteral(1), nil))
    val list2 = CaseClass(consType, Seq(IntLiteral(2), list1))
    val list3 = CaseClass(consType, Seq(IntLiteral(3), list2))

    Equals(FunctionInvocation(size, Seq(list3)), IntLiteral(3))
  }

  assertValid(intSize)

  assertValid(And(booleanSize, intSize))
}
