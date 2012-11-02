package leon
package synthesis

import purescala.Common._
import purescala.Trees._
import purescala.Extractors._
import purescala.TreeOps._
import purescala.TypeTrees._
import purescala.Definitions._

object Heuristics {
  def all(synth: Synthesizer) = Set(
    new OptimisticGround(synth),
    new IntInduction(synth)
  )
}

class OptimisticGround(synth: Synthesizer) extends Rule("Optimistic Ground", synth, 9, 0) {
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
        synth.solver.solveSAT(phi) match {
          case (Some(true), satModel) =>
            val satXsModel = satModel.filterKeys(xss) 

            val newPhi = valuateWithModelIn(phi, xss, satModel)

            synth.solver.solveSAT(Not(newPhi)) match {
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


class IntInduction(synth: Synthesizer) extends Rule("Int Induction", synth, 8, 500) {
  def applyOn(task: Task): RuleResult = {
    val p = task.problem

    p.as match {
      case List(origId) if origId.getType == Int32Type =>
        val tpe = TupleType(p.xs.map(_.getType))

        val inductOn = FreshIdentifier(origId.name, true).setType(origId.getType)

        val postXs  = p.xs map (id => FreshIdentifier("r", true).setType(id.getType))

        val postXsMap = (p.xs zip postXs).toMap.mapValues(Variable(_))

        val newPhi     = subst(origId -> Variable(inductOn), p.phi)
        val postCondGT = substAll(postXsMap + (origId -> Minus(Variable(inductOn), IntLiteral(1))), p.phi)
        val postCondLT = substAll(postXsMap + (origId -> Plus(Variable(inductOn), IntLiteral(1))), p.phi)

        val subBase = Problem(List(), subst(origId -> IntLiteral(0), p.phi), p.xs)
        val subGT   = Problem(inductOn :: postXs, And(Seq(newPhi, GreaterThan(Variable(inductOn), IntLiteral(0)), postCondGT)), p.xs)
        val subLT   = Problem(inductOn :: postXs, And(Seq(newPhi, LessThan(Variable(inductOn), IntLiteral(0)), postCondLT)), p.xs)

        val onSuccess: List[Solution] => Solution = {
          case List(base, gt, lt) =>
            val newFun = new FunDef(FreshIdentifier("rec", true), tpe, Seq(VarDecl(inductOn, inductOn.getType)))
            newFun.body = Some( 
              IfExpr(Equals(Variable(inductOn), IntLiteral(0)),
                base.toExpr,
              IfExpr(GreaterThan(Variable(inductOn), IntLiteral(0)),
                LetTuple(postXs, FunctionInvocation(newFun, Seq(Minus(Variable(inductOn), IntLiteral(1)))), gt.toExpr)
              , LetTuple(postXs, FunctionInvocation(newFun, Seq(Plus(Variable(inductOn), IntLiteral(1)))), lt.toExpr)))
            )

            Solution(BooleanLiteral(true), LetDef(newFun, FunctionInvocation(newFun, Seq(Variable(origId)))))
          case _ =>
            Solution.none
        }

        RuleDecomposed(List(subBase, subGT, subLT), onSuccess)
      case _ =>
        RuleInapplicable
    }
  }
}
