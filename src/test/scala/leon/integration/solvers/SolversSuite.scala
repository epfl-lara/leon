/* Copyright 2009-2016 EPFL, Lausanne */

package leon.integration.solvers

import leon.test._
import leon.purescala.Common._
import leon.purescala.Definitions._
import leon.purescala.ExprOps._
import leon.purescala.Constructors._
import leon.purescala.Expressions._
import leon.purescala.Types._
import leon.LeonContext

import leon.solvers._
import leon.solvers.smtlib._
import leon.solvers.z3._

class SolversSuite extends LeonTestSuiteWithProgram {

  val sources = List()

  val solverNames: Seq[String] = {
    (if (SolverFactory.hasNativeZ3) Seq("fairz3") else Nil) ++
    (if (SolverFactory.hasZ3)       Seq("smt-z3") else Nil) ++
    (if (SolverFactory.hasCVC4)     Seq("smt-cvc4") else Nil)
  }

  val types = Seq(
    BooleanType,
    UnitType,
    CharType,
    RealType,
    IntegerType,
    Int32Type,
    StringType,
    TypeParameter.fresh("T"),
    SetType(IntegerType),
    BagType(IntegerType),
    MapType(IntegerType, IntegerType),
    FunctionType(Seq(IntegerType), IntegerType),
    TupleType(Seq(IntegerType, BooleanType, Int32Type))
  )

  val vs = types.map(FreshIdentifier("v", _).toVariable)

  // We need to make sure models are not co-finite
  val cnstrs = vs.map(v => v.getType match {
    case UnitType =>
      Equals(v, simplestValue(v.getType))
    case SetType(base) =>
      Not(ElementOfSet(simplestValue(base), v))
    case BagType(base) =>
      Not(Equals(MultiplicityInBag(simplestValue(base), v), simplestValue(IntegerType)))
    case MapType(from, to) =>
      Not(Equals(MapApply(v, simplestValue(from)), simplestValue(to)))
    case FunctionType(froms, to) =>
      Not(Equals(Application(v, froms.map(simplestValue)), simplestValue(to)))
    case _ =>
      not(Equals(v, simplestValue(v.getType)))
  })

  def checkSolver(solver: Solver, vs: Set[Variable], cnstr: Expr)(implicit fix: (LeonContext, Program)): Unit = {
    try {
      solver.assertCnstr(cnstr)

      solver.check match {
        case Some(true) =>
          val model = solver.getModel
          for (v <- vs) {
            if (model.isDefinedAt(v.id)) {
              assert(model(v.id).getType === v.getType, s"Solver $solver - Extracting value of type "+v.getType)
            } else {
              fail(s"Solver $solver - Model does not contain "+v.id.uniqueName+" of type "+v.getType)
            }
          }
        case res =>
          fail(s"Solver $solver - Constraint "+cnstr.asString+" is unsat!? Solver was "+solver.getClass)
      }
    } finally {
      solver.free()
    }
  }

  // Check that we correctly extract several types from solver models
  for (sname <- solverNames) {
    test(s"Model Extraction in $sname") { implicit fix =>
      val ctx = fix._1
      val pgm = fix._2
      val solver = SolverFactory.getFromName(ctx, pgm)(sname).getNewSolver()
      checkSolver(solver, vs.toSet, andJoin(cnstrs))
    }
  }

  test(s"Data generation in enum solver") { implicit fix =>
    for ((v,cnstr) <- vs zip cnstrs) {
      val solver = new EnumerationSolver(fix._1.toSctx, fix._2)
      checkSolver(solver, Set(v), cnstr)
    }
  }
}
