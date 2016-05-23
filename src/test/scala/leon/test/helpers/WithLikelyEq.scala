/* Copyright 2009-2016 EPFL, Lausanne */

package leon.test.helpers

import org.scalatest.Assertions

import leon.test._
import leon.evaluators._
import leon.purescala.Common._
import leon.LeonContext
import leon.purescala.Types._
import leon.purescala.Definitions._
import leon.purescala.ExprOps._
import leon.purescala.Expressions._
import leon.utils.SeqUtils._

/*
 * Determine if two expressions over arithmetic variables are likely to be equal.
 *
 * This is a probabilistic based approach, it does not rely on any external solver and can
 * only prove the non equality of two expressions.
 */
trait WithLikelyEq {
  self: Assertions =>

  val typesValues = Map[TypeTree, Seq[Expr]](
    IntegerType -> Seq(-42, -1, 0, 1, 7, 42).map(InfiniteIntegerLiteral(_)),
    Int32Type   -> Seq(-42, -1, 0, 1, 7, 42).map(IntLiteral(_)),
    BooleanType -> Seq(BooleanLiteral(false), BooleanLiteral(true))
  )

  def checkLikelyEq(ctx: LeonContext, pgm: Program = Program.empty)(e1: Expr, e2: Expr, pre: Option[Expr] = None, values: Map[Identifier, Expr] = Map()): Unit = {
    val evaluator = new DefaultEvaluator(ctx, pgm)

    val freeVars = (variablesOf(e1) ++ variablesOf(e2)).toSeq.sorted

    if (freeVars.isEmpty) {
      val r1 = evaluator.eval(e1)
      val r2 = evaluator.eval(e2)

      assert(r1 === r2, s"'$e1' != '$e2' ('$r1' != '$r2')")
    } else {

      val allValues = freeVars.map(id => values.get(id).map(Seq(_)).getOrElse(typesValues(id.getType)))

      cartesianProduct(allValues).foreach { vs =>
        val m = evaluator.evalEnv(freeVars zip vs)
        val doTest = pre.map { p =>
          evaluator.eval(p, m).result match {
            case Some(BooleanLiteral(b)) => b
            case _ => fail("Precondition is not a boolean expression")
          }
        }.getOrElse(true)

        if (doTest) {
          val r1 = evaluator.eval(e1, m)
          val r2 = evaluator.eval(e2, m)

          assert(r1 === r2, s"'$e1' != '$e2' with '$m' ('$r1' != '$r2')")
        }
      }
    }
  }
}
