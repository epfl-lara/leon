/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package synthesis

import purescala.Expressions._
import purescala.ExprOps._

/** A named way of computing the cost of problem and solutions.*/
abstract class CostModel(val name: String) {
  def solution(s: Solution): Cost

  def impossible: Cost

  def isImpossible(c: Cost): Boolean = {
    c >= impossible
  }
}

/** Represents a cost used when comparing synthesis solutions for example */
case class Cost(minSize: Int) extends AnyVal with Ordered[Cost] {
  def compare(that: Cost): Int = {
    this.minSize-that.minSize
  }

  override def toString: String = {
    f"$minSize%3d"
  }
}

/** Contains all and the default [CostModel] */
object CostModels {
  def default: CostModel = NaiveCostModel

  def all: Set[CostModel] = Set(
    NaiveCostModel,
    WeightedBranchesCostModel
  )
}

/** Wrapped cost model. Not used at this moment. */
class WrappedCostModel(cm: CostModel, name: String) extends CostModel(name) {

  def solution(s: Solution): Cost = cm.solution(s)

  def impossible = cm.impossible
}

/** Computes a cost corresponding of the size of the solution expression divided by 10.
  * For problems, returns a cost of 1 */
class SizeBasedCostModel(name: String) extends CostModel(name) {
  def solution(s: Solution) = {
    Cost(formulaSize(s.term))
  }

  def impossible = Cost(1000)
}

case object NaiveCostModel extends SizeBasedCostModel("Naive")

case object WeightedBranchesCostModel extends SizeBasedCostModel("WeightedBranches") {

  def branchesCost(e: Expr): Int = {
    case class BC(cost: Int, nesting: Int)

    def pre(e: Expr, c: BC) = {
      (e, c.copy(nesting = c.nesting + 1))
    }

    def costOfBranches(alts: Int, nesting: Int) = {
      if (nesting > 10) {
        alts
      } else {
        (10-nesting)*alts
      }
    }

    def post(e: Expr, bc: BC) = e match {
      case ie : IfExpr =>
       (e, bc.copy(cost = bc.cost + costOfBranches(2, bc.nesting)))
      case ie : LetDef => 
       (e, bc.copy(cost = bc.cost + costOfBranches(2, bc.nesting)))
      case ie : MatchExpr => 
       (e, bc.copy(cost = bc.cost + costOfBranches(ie.cases.size, bc.nesting)))
      case _ => 
       (e, bc)
    }

    def combiner(e: Expr, cs: Seq[BC]) = {
      cs.foldLeft(BC(0,0))((bc1, bc2) => BC(bc1.cost + bc2.cost, 0))
    }

    val (_, bc) = genericTransform[BC](pre, post, combiner)(BC(0, 0))(e)

    bc.cost
  }

  override def solution(s: Solution) = {
    Cost(formulaSize(s.toExpr) + branchesCost(s.toExpr))
  }

}
