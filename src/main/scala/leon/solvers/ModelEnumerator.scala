package leon
package solvers

import purescala.Definitions._
import purescala.Common._
import purescala.Expressions._
import purescala.Constructors._
import purescala.ExprOps._
import purescala.Types._
import evaluators._


class ModelEnumerator(ctx: LeonContext, pgm: Program, sf: SolverFactory[IncrementalSolver]) {
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

  private[this] def enumVarying0(ids: Seq[Identifier], cnstr: Expr, caracteristic: Option[Expr], nPerCaracteristic: Int = 1): Iterator[Map[Identifier, Expr]] = {
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

  def enumMinimizing(ids: Seq[Identifier], cnstr: Expr, measure: Expr) = {
    enumOptimizing(ids, cnstr, measure, Down)
  }

  def enumMaximizing(ids: Seq[Identifier], cnstr: Expr, measure: Expr) = {
    enumOptimizing(ids, cnstr, measure, Up)
  }

  abstract class SearchDirection
  case object Up   extends SearchDirection
  case object Down extends SearchDirection

  private[this] def enumOptimizing(ids: Seq[Identifier], cnstr: Expr, measure: Expr, dir: SearchDirection): Iterator[Map[Identifier, Expr]] = {
    assert(measure.getType == IntegerType)

    val s = sf.getNewSolver
    reclaimPool ::= s

    s.assertCnstr(cnstr)

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
        val thisTry = getPivot().map { t =>
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
            val m = (ids.map { id =>
              id -> sm.getOrElse(id, simplestValue(id.getType))
            }).toMap

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
