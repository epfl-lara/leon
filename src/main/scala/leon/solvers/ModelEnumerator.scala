package leon
package solvers

import purescala.Definitions._
import purescala.Common._
import purescala.Expressions._
import purescala.Constructors._
import purescala.ExprOps._
import purescala.Types._
import evaluators._


class ModelEnumerator(ctx: LeonContext, pgm: Program, sf: SolverFactory[Solver]) {
  private[this] var reclaimPool = List[Solver]()
  private[this] val evaluator = new DefaultEvaluator(ctx, pgm)

  def enumSimple(ids: Seq[Identifier], cnstr: Expr): Iterator[Map[Identifier, Expr]] = {
    enumVarying0(ids, cnstr, None, -1)
  }

  /**
   * Enumerate at most `nPerCaracteristic` models with the same value for
   * `caracteristic`.
   *
   * Note: there is no guarantee that the models enumerated consecutively share the
   * same `caracteristic`.
   */
  def enumVarying(ids: Seq[Identifier], cnstr: Expr, caracteristic: Expr, nPerCaracteristic: Int = 1) = {
    enumVarying0(ids, cnstr, Some(caracteristic), nPerCaracteristic)
  }

  def enumVarying0(ids: Seq[Identifier], cnstr: Expr, caracteristic: Option[Expr], nPerCaracteristic: Int = 1): Iterator[Map[Identifier, Expr]] = {
    val s = sf.getNewSolver
    reclaimPool ::= s

    s.assertCnstr(cnstr)

    val c = caracteristic match {
      case Some(car) =>
        val c = FreshIdentifier("car", car.getType)
        s.assertCnstr(Equals(c.toVariable, car))
        c
      case None =>
        FreshIdentifier("noop", BooleanType)
    }

    var perCarRemaining = Map[Expr, Int]()

    new Iterator[Map[Identifier, Expr]] {
      def hasNext = {
        s.check == Some(true)
      }

      def next = {
        val sm = s.getModel
        val m = (ids.map { id =>
          id -> sm.getOrElse(id, simplestValue(id.getType))
        }).toMap


        // Vary the model
        s.assertCnstr(not(andJoin(m.toSeq.sortBy(_._1).map { case (k,v) => equality(k.toVariable, v) })))

        caracteristic match {
          case Some(car) =>
            val cValue = evaluator.eval(car, m).result.get

            perCarRemaining += (cValue -> (perCarRemaining.getOrElse(cValue, nPerCaracteristic) - 1))
            if (perCarRemaining(cValue) == 0) {
              s.assertCnstr(not(equality(c.toVariable, cValue)))
            }

          case None =>
        }

        m
      }
    }
  }

  def shutdown() = {
    reclaimPool.foreach{sf.reclaim(_)}
  }

}
