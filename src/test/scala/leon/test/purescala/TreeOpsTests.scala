/* Copyright 2009-2013 EPFL, Lausanne */

package leon.test.purescala

import leon.LeonContext
import leon.SilentReporter

import leon.purescala.Common._
import leon.purescala.Definitions._
import leon.purescala.Trees._
import leon.purescala.TypeTrees._
import leon.purescala.TreeOps._

import org.scalatest.FunSuite

class TreeOpsTests extends FunSuite {
  private val silentContext = LeonContext(reporter = new SilentReporter)
  
  test("Path-aware simplifications") {
    import leon.solvers.z3.UninterpretedZ3Solver
    val solver = new UninterpretedZ3Solver(silentContext)
    solver.setProgram(Program.empty)

    // TODO actually testing something here would be better, sorry
    // PS

    assert(true)  
  }


  def i(x: Int) = IntLiteral(x)

  val xId = FreshIdentifier("x").setType(Int32Type)
  val x = Variable(xId)
  val yId = FreshIdentifier("y").setType(Int32Type)
  val y = Variable(yId)
  val xs = Set(xId, yId)

  val aId = FreshIdentifier("a").setType(Int32Type)
  val a = Variable(aId)
  val bId = FreshIdentifier("b").setType(Int32Type)
  val b = Variable(bId)
  val as = Set(aId, bId)

  def checkSameExpr(e1: Expr, e2: Expr, vs: Set[Identifier]) {
    assert( //this outer assert should not be needed because of the nested one
      LikelyEq(e1, e2, vs, BooleanLiteral(true), (e1, e2) => {assert(e1 === e2); true})
    )
  }

  test("simplifyArithmetic") {
    val e1 = Plus(IntLiteral(3), IntLiteral(2))
    checkSameExpr(e1, simplifyArithmetic(e1), Set())
    val e2 = Plus(x, Plus(IntLiteral(3), IntLiteral(2)))
    checkSameExpr(e2, simplifyArithmetic(e2), Set(xId))

    val e3 = Minus(IntLiteral(3), IntLiteral(2))
    checkSameExpr(e3, simplifyArithmetic(e3), Set())
    val e4 = Plus(x, Minus(IntLiteral(3), IntLiteral(2)))
    checkSameExpr(e4, simplifyArithmetic(e4), Set(xId))
    val e5 = Plus(x, Minus(x, IntLiteral(2)))
    checkSameExpr(e5, simplifyArithmetic(e5), Set(xId))

    val e6 = Times(IntLiteral(9), Plus(Division(x, IntLiteral(3)), Division(x, IntLiteral(6))))
    checkSameExpr(e6, simplifyArithmetic(e6), Set(xId))
  }

  test("expandAndSimplifyArithmetic") {
    val e1 = Plus(IntLiteral(3), IntLiteral(2))
    checkSameExpr(e1, expandAndSimplifyArithmetic(e1), Set())
    val e2 = Plus(x, Plus(IntLiteral(3), IntLiteral(2)))
    checkSameExpr(e2, expandAndSimplifyArithmetic(e2), Set(xId))

    val e3 = Minus(IntLiteral(3), IntLiteral(2))
    checkSameExpr(e3, expandAndSimplifyArithmetic(e3), Set())
    val e4 = Plus(x, Minus(IntLiteral(3), IntLiteral(2)))
    checkSameExpr(e4, expandAndSimplifyArithmetic(e4), Set(xId))
    val e5 = Plus(x, Minus(x, IntLiteral(2)))
    checkSameExpr(e5, expandAndSimplifyArithmetic(e5), Set(xId))

    val e6 = Times(IntLiteral(9), Plus(Division(x, IntLiteral(3)), Division(x, IntLiteral(6))))
    checkSameExpr(e6, expandAndSimplifyArithmetic(e6), Set(xId))
  }

  test("extractEquals") {
    val eq = Equals(a, b)
    val lt1 = LessThan(a, b)
    val lt2 = LessThan(b, a)
    val lt3 = LessThan(x, y)

    val f1 = And(Seq(eq, lt1, lt2, lt3))
    val (eq1, r1) = extractEquals(f1)
    assert(eq1 != None)
    assert(eq1.get === eq)
    assert(extractEquals(r1)._1 === None)

    val f2 = And(Seq(lt1, lt2, eq, lt3))
    val (eq2, r2) = extractEquals(f2)
    assert(eq2 != None)
    assert(eq2.get === eq)
    assert(extractEquals(r2)._1 === None)

    val f3 = And(Seq(lt1, eq, lt2, lt3, eq))
    val (eq3, r3) = extractEquals(f3)
    assert(eq3 != None)
    assert(eq3.get === eq)
    val (eq4, r4) = extractEquals(r3)
    assert(eq4 != None)
    assert(eq4.get === eq)
    assert(extractEquals(r4)._1 === None)

  }
}
