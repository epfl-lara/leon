package leon.test.purescala

import leon.purescala.Common._
import leon.purescala.Definitions._
import leon.purescala.Trees._
import leon.purescala.TreeOps._
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
}
