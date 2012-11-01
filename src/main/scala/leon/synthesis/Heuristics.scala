package leon
package synthesis

import purescala.Common._
import purescala.Trees._
import purescala.Extractors._
import purescala.TreeOps._
import purescala.TypeTrees._

object Heuristics {
  def all(synth: Synthesizer) = Set(
    new IntInduction(synth)
  )
}

class OptimisticGround(synth: Synthesizer) extends Rule("Optimistic Ground", synth, 90) {
  def applyOn(task: Task): RuleResult = {
    val p = task.problem

    if (!p.as.isEmpty && !p.xs.isEmpty) {
      val xss = p.xs.toSet
      val ass = p.as.toSet

      val tpe = TupleType(p.xs.map(_.getType))

      var i = 0;
      var maxTries = 3;

      var result: Option[RuleResult]   = None
      var predicates: Seq[Expr]        = Seq()

      while (result.isEmpty && i < maxTries) {
        val phi = And(p.phi +: predicates)
        synth.solveSAT(phi) match {
          case (Some(true), satModel) =>
            val satXsModel = satModel.filterKeys(xss) 

            val newPhi = valuateWithModelIn(phi, xss, satModel)

            synth.solveSAT(Not(newPhi)) match {
              case (Some(true), invalidModel) =>
                // Found as such as the xs break, refine predicates
                predicates = valuateWithModelIn(phi, ass, invalidModel) +: predicates

              case (Some(false), _) =>
                result = Some(RuleSuccess(Solution(BooleanLiteral(true), Tuple(p.xs.map(valuateWithModel(satModel))).setType(tpe))))

              case _ =>
                result = Some(RuleInapplicable)
            }

          case (Some(false), _) =>
            if (predicates.isEmpty) {
              result = Some(RuleSuccess(Solution(BooleanLiteral(false), Error(p.phi+" is UNSAT!").setType(tpe))))
            } else {
              result = Some(RuleInapplicable)
            }
          case _ =>
            result = Some(RuleInapplicable)
        }

        i += 1 
      }

      result.getOrElse(RuleInapplicable)
    } else {
      RuleInapplicable
    }
  }
}


class IntInduction(synth: Synthesizer) extends Rule("Int Induction", synth, 80) {
  def applyOn(task: Task): RuleResult = {
    val p = task.problem

    p.as.find(_.getType == Int32Type) match {
      case Some(inductOn) =>
              
        val subBase = Problem(p.as.filterNot(_ == inductOn), subst(inductOn -> IntLiteral(0), p.phi), p.xs)
      //  val subGT   = Problem(p.as + tmpGT, And(Seq(p.phi, GreaterThan(Variable(inductOn), IntLiteral(0)), subst(inductOn -> IntLiteral(0), p.phi), p.xs)

        RuleDecomposed(List(subBase), forward)
      case None =>
        RuleInapplicable
    }
  }
}
