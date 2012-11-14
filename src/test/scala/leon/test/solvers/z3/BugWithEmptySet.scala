package leon.test.solvers.z3

import leon.purescala.Common._
import leon.purescala.Definitions._
import leon.purescala.Trees._
import leon.purescala.TreeOps._
import leon.purescala.TypeTrees._

import leon.SilentReporter

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

    val formula = Equals(e1, e2)

    val silentReporter = new SilentReporter
    val solver : Solver = new UninterpretedZ3Solver(silentReporter)
    solver.setProgram(emptyProgram)

    assert(solver.solve(formula) === Some(true),
           "Z3 should prove the equivalence between Ø and {}.")
  } 
}
