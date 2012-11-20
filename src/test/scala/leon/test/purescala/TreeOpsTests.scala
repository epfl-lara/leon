package leon.test.purescala

import leon.purescala.Common._
import leon.purescala.Definitions._
import leon.purescala.Trees._
import leon.purescala.TreeOps._
import leon.purescala.LikelyEq
import leon.SilentReporter

import org.scalatest.FunSuite

class TreeOpsTests extends FunSuite {
  private val silentReporter = new SilentReporter
  
  private val emptyProgram = Program(
    FreshIdentifier("Empty"),
    ObjectDef(FreshIdentifier("Empty"), Seq.empty, Seq.empty)
  )

  test("Path-aware simplifications") {
    import leon.solvers.z3.UninterpretedZ3Solver
    val solver = new UninterpretedZ3Solver(silentReporter)
    solver.setProgram(emptyProgram)

    // TODO actually testing something here would be better, sorry
    // PS

    assert(true)  
  }


  def i(x: Int) = IntLiteral(x)

  val xId = FreshIdentifier("x")
  val x = Variable(xId)
  val yId = FreshIdentifier("y")
  val y = Variable(yId)
  val xs = Set(xId, yId)

  val aId = FreshIdentifier("a")
  val a = Variable(aId)
  val bId = FreshIdentifier("b")
  val b = Variable(bId)
  val as = Set(aId, bId)

  def checkSameExpr(e1: Expr, e2: Expr, vs: Set[Identifier]) {
    assert( //this outer assert should not be needed because of the nested one
      LikelyEq(e1, e2, vs, BooleanLiteral(true), (e1, e2) => {assert(e1 === e2); true})
    )
  }

  test("simplifyArithmetic") {
    val e1 = Plus(IntLiteral(3), IntLiteral(2))
    checkSameExpr(e1, simplify(e1), Set())
    val e2 = Plus(x, Plus(IntLiteral(3), IntLiteral(2)))
    checkSameExpr(e2, simplify(e2), Set(xId))

    val e3 = Minus(IntLiteral(3), IntLiteral(2))
    checkSameExpr(e3, simplify(e3), Set())
    val e4 = Plus(x, Minus(IntLiteral(3), IntLiteral(2)))
    checkSameExpr(e4, simplify(e4), Set(xId))
    val e5 = Plus(x, Minus(x, IntLiteral(2)))
    checkSameExpr(e5, simplify(e5), Set(xId))
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
