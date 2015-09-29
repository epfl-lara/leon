/* Copyright 2009-2015 EPFL, Lausanne */

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
import leon.solvers.combinators._
import leon.solvers.z3._

class SolversSuite extends LeonTestSuiteWithProgram {

  val sources = List()

  val getFactories: Seq[(String, (LeonContext, Program) => Solver)] = {
    (if (SolverFactory.hasNativeZ3) Seq(
      ("fairz3",   (ctx: LeonContext, pgm: Program) => new FairZ3Solver(ctx, pgm))
    ) else Nil) ++
    (if (SolverFactory.hasZ3)       Seq(
      ("smt-z3",   (ctx: LeonContext, pgm: Program) => new UnrollingSolver(ctx, pgm, new SMTLIBZ3Solver(ctx, pgm)))
    ) else Nil) ++
    (if (SolverFactory.hasCVC4)     Seq(
      ("smt-cvc4", (ctx: LeonContext, pgm: Program) => new UnrollingSolver(ctx, pgm, new SMTLIBCVC4Solver(ctx, pgm)))
    ) else Nil)
  }

  // Check that we correctly extract several types from solver models
  for ((sname, sf) <- getFactories) {
    test(s"Model Extraction in $sname") { implicit fix =>
      val ctx = fix._1
      val pgm = fix._2

      val solver = sf(ctx, pgm)

      val types = Seq(
        BooleanType,
        UnitType,
        CharType,
        IntegerType,
        Int32Type,
        TypeParameter.fresh("T"),
        SetType(IntegerType),
        MapType(IntegerType, IntegerType),
        TupleType(Seq(IntegerType, BooleanType, Int32Type))
      )

      val vs = types.map(FreshIdentifier("v", _).toVariable)


      // We need to make sure models are not co-finite
      val cnstr = andJoin(vs.map(v => v.getType match {
        case UnitType =>
          Equals(v, simplestValue(v.getType))
        case SetType(base) =>
          Not(ElementOfSet(simplestValue(base), v))
        case MapType(from, to) =>
          Not(Equals(MapApply(v, simplestValue(from)), simplestValue(to)))
        case _ =>
          not(Equals(v, simplestValue(v.getType)))
      }))

      try {
        solver.assertCnstr(cnstr)

        solver.check match {
          case Some(true) =>
            val model = solver.getModel
            for (v <- vs) {
              if (model.isDefinedAt(v.id)) {
                assert(model(v.id).getType === v.getType, "Extracting value of type "+v.getType)
              } else {
                fail("Model does not contain "+v.id+" of type "+v.getType)
              }
            }
          case _ =>
            fail("Constraint "+cnstr.asString+" is unsat!?")
        }
      } finally {
        solver.free
      }

    }
  }
}
