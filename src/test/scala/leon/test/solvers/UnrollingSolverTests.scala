package leon.test.solvers

import leon._
import leon.test._
import leon.purescala.Trees._
import leon.purescala.TypeTrees._
import leon.purescala.Common._
import leon.purescala.Definitions._
import leon.solvers._
import leon.solvers.z3._
import leon.solvers.combinators._

class UnrollingSolverTests extends LeonTestSuite {

  private val fx   : Identifier = FreshIdentifier("x").setType(IntegerType)
  private val fres : Identifier = FreshIdentifier("res").setType(IntegerType)
  private val fDef : FunDef = new FunDef(FreshIdentifier("f"), Nil, IntegerType, ValDef(fx, IntegerType) :: Nil, DefType.MethodDef)
  fDef.body = Some(IfExpr(GreaterThan(Variable(fx), InfiniteIntegerLiteral(0)),
    Plus(Variable(fx), FunctionInvocation(fDef.typed, Seq(Minus(Variable(fx), InfiniteIntegerLiteral(1))))),
    InfiniteIntegerLiteral(1)
  ))
  fDef.postcondition = Some(fres -> GreaterThan(Variable(fres), InfiniteIntegerLiteral(0)))

  private val program = Program(
    FreshIdentifier("Minimal"),
    List(UnitDef(
      FreshIdentifier("Minimal"),
      List(ModuleDef(FreshIdentifier("Minimal"), Seq(fDef), false))
    ))
  )

  private val sf = SolverFactory(() => new UnrollingSolver(testContext, program, new UninterpretedZ3Solver(testContext, program)))
  private def check(expr: Expr, expected: Option[Boolean], msg: String) : Unit = {
    test(msg) {
      val solver = sf.getNewSolver
      solver.assertCnstr(expr)
      assert(solver.check == expected)
      solver.free
    }
  }

  check(BooleanLiteral(true), Some(true), "'true' should always be valid")
  check(BooleanLiteral(false), Some(false), "'false' should never be valid")

  check(Not(GreaterThan(FunctionInvocation(fDef.typed, Seq(Variable(FreshIdentifier("toto").setType(IntegerType)))), InfiniteIntegerLiteral(0))),
    Some(false), "unrolling should enable recursive definition verification")
}
