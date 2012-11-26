package leon.test.solvers.z3

import leon.LeonContext
import leon.SilentReporter

import leon.purescala.Common._
import leon.purescala.Definitions._
import leon.purescala.Trees._
import leon.purescala.TreeOps._
import leon.purescala.TypeTrees._

import leon.solvers.Solver
import leon.solvers.z3.UninterpretedZ3Solver

import org.scalatest.FunSuite

class BugWithEmptySet extends FunSuite {
  private val emptyProgram = Program(FreshIdentifier("empty"), ObjectDef(FreshIdentifier("empty"), Nil, Nil))

  test("No distinction between Set() and Set.empty") {
    val tInt = Int32Type
    val tIntSet = SetType(Int32Type)

    val e1 = EmptySet(tInt).setType(tIntSet)
    assert(e1.getType === tIntSet)

    val e2 = FiniteSet(Nil).setType(tIntSet)
    assert(e2.getType === tIntSet)

    val s0 = FiniteSet(Seq(IntLiteral(0))).setType(tIntSet)

    val f1 = Equals(e1, e2)

    val silentContext = LeonContext(reporter = new SilentReporter)
    val solver : Solver = new UninterpretedZ3Solver(silentContext)
    solver.setProgram(emptyProgram)

    assert(solver.solve(f1) === Some(true),
           "Z3 should prove the equivalence between Ø and {}.")

    val f2 = Equals(e1, SetDifference(e1, s0))

    assert(solver.solve(f2) === Some(true),
           """Z3 should prove Ø = Ø \ {0}""")

    val f3 = Equals(e2, SetDifference(e2, s0))

    assert(solver.solve(f3) === Some(true),
           """Z3 should prove {} = {} \ {0}""")
  } 
}
