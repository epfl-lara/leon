package leon
package utils

import purescala.Definitions._
import purescala.Common._
import purescala.Expressions._
import purescala.Constructors._
import purescala.ExprOps._
import purescala.Types._
import evaluators._
import solvers._

class ModelEnumerator(ctx: LeonContext, pgm: Program, sf: SolverFactory[Solver]) {
  private[this] var reclaimPool = List[Solver]()
  private[this] val evaluator = new DefaultEvaluator(ctx, pgm)

  def enumSimple(ids: Seq[Identifier], satisfying: Expr): Iterator[Map[Identifier, Expr]] = {
    enumVarying0(ids, satisfying, None, -1)
  }

  /**
   * Enumerate at most `nPerCaracteristic` models with the same value for
   * `caracteristic`.
   *
   * Note: there is no guarantee that the models enumerated consecutively share the
   * same `caracteristic`.
   */
  def enumVarying(ids: Seq[Identifier], satisfying: Expr, measure: Expr, nPerMeasure: Int = 1) = {
    enumVarying0(ids, satisfying, Some(measure), nPerMeasure)
  }

  private[this] def enumVarying0(ids: Seq[Identifier], satisfying: Expr, measure: Option[Expr], nPerMeasure: Int = 1): Iterator[Map[Identifier, Expr]] = {
    val s = sf.getNewSolver
    reclaimPool ::= s

    s.assertCnstr(satisfying)

    val m = measure match {
      case Some(ms) =>
        val m = FreshIdentifier("measure", ms.getType)
        s.assertCnstr(Equals(m.toVariable, ms))
        m
      case None =>
        FreshIdentifier("noop", BooleanType)
    }

    var perMeasureRem = Map[Expr, Int]().withDefaultValue(nPerMeasure)

    new Iterator[Map[Identifier, Expr]] {
      def hasNext = {
        s.check == Some(true)
      }

      def next() = {
        val sm = s.getModel
        val model = ids.map { id =>
          id -> sm.getOrElse(id, simplestValue(id.getType))
        }.toMap


        // Vary the model
        s.assertCnstr(not(andJoin(model.toSeq.sortBy(_._1).map { case (k,v) => equality(k.toVariable, v) })))

        measure match {
          case Some(ms) =>
            val mValue = evaluator.eval(ms, model).result.get

            perMeasureRem += (mValue -> (perMeasureRem(mValue) - 1))

            if (perMeasureRem(mValue) <= 0) {
              s.assertCnstr(not(equality(m.toVariable, mValue)))
            }

          case None =>
        }

        model
      }
    }
  }

  def enumMinimizing(ids: Seq[Identifier], cnstr: Expr, measure: Expr) = {
    enumOptimizing(ids, cnstr, measure, Down)
  }

  def enumMaximizing(ids: Seq[Identifier], cnstr: Expr, measure: Expr) = {
    enumOptimizing(ids, cnstr, measure, Up)
  }

  abstract class SearchDirection
  case object Up   extends SearchDirection
  case object Down extends SearchDirection

  private[this] def enumOptimizing(ids: Seq[Identifier], satisfying: Expr, measure: Expr, dir: SearchDirection): Iterator[Map[Identifier, Expr]] = {
    assert(measure.getType == IntegerType)

    val s = sf.getNewSolver
    reclaimPool ::= s

    s.assertCnstr(satisfying)

    val mId = FreshIdentifier("measure", measure.getType)
    s.assertCnstr(Equals(mId.toVariable, measure))

    // Search Range
    var ub: Option[BigInt] = None
    var lb: Option[BigInt] = None

    def rangeEmpty() = (lb, ub) match {
      case (Some(l), Some(u)) => u-l <= 1
      case _ => false
    }

    def getPivot(): Option[BigInt] = (lb, ub, dir) match {
      // Bisection Method
      case (Some(l), Some(u), _) => Some(l + (u-l)/2)
      // No bound yet, let the solver find at least one bound
      case (None, None, _)       => None

      // Increase lower bound
      case (Some(l), None, Up)   => Some(l + l.abs + 1)
      // Decrease upper bound
      case (None, Some(u), Down) => Some(u - u.abs - 1)

      // This shouldn't happen
      case _ => None
    }

    def getNext(): Stream[Map[Identifier, Expr]] = {
      if (rangeEmpty()) {
        Stream.empty
      } else {
        // Assert a new pivot point
        val thisTry = getPivot()
        thisTry.foreach { t =>
          s.push()
          dir match {
            case Up =>
              s.assertCnstr(GreaterThan(mId.toVariable, InfiniteIntegerLiteral(t)))
            case Down =>
              s.assertCnstr(LessThan(mId.toVariable, InfiniteIntegerLiteral(t)))
          }
          t
        }

        s.check match {
          case Some(true) =>
            val sm = s.getModel
            val m = ids.map { id =>
              id -> sm.getOrElse(id, simplestValue(id.getType))
            }.toMap

            evaluator.eval(measure, m).result match {
              case Some(InfiniteIntegerLiteral(measureVal)) =>
                // Positive result
                dir match {
                  case Up   => lb = Some(measureVal)
                  case Down => ub = Some(measureVal)
                }

                Stream.cons(m, getNext())

              case _ =>
                ctx.reporter.warning("Evaluator failed to evaluate measure!")
                Stream.empty
            }


          case Some(false) =>
            // Negative result
            thisTry match {
              case Some(t) =>
                s.pop()

                dir match {
                  case Up   => ub = Some(t)
                  case Down => lb = Some(t)
                }
                getNext()

              case None =>
                Stream.empty
            }

          case None =>
            Stream.empty
        }
      }
    }

    getNext().iterator
  }


  def shutdown() = {
    reclaimPool.foreach(sf.reclaim)
  }

}
