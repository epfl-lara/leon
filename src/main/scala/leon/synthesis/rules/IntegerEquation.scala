package leon
package synthesis
package rules

import purescala.Common._
import purescala.Trees._
import purescala.Extractors._
import purescala.TreeOps._
import purescala.TypeTrees._
import purescala.Definitions._
import LinearEquations.elimVariable
import ArithmeticNormalization.simplify

class IntegerEquation(synth: Synthesizer) extends Rule("Integer Equation", synth, 300) {
  def applyOn(task: Task): RuleResult = {

    val p = task.problem

    val TopLevelAnds(exprs) = p.phi
    val xs = p.xs
    val as = p.as
    val formula = p.phi

    val (eqs, others) = exprs.partition(_.isInstanceOf[Equals])
    var candidates: Seq[Expr] = eqs
    var allOthers: Seq[Expr] = others

    var vars: Set[Identifier] = Set()
    var eqas: Set[Identifier] = Set()
    var eqxs: List[Identifier] = List()
    var ys: Set[Identifier] = Set()

    var optionNormalizedEq: Option[List[Expr]] = None
    while(!candidates.isEmpty && optionNormalizedEq == None) {
      val eq@Equals(_,_) = candidates.head
      candidates = candidates.tail
      
      vars = variablesOf(eq)
      eqas = as.toSet.intersect(vars)

      eqxs = xs.toSet.intersect(vars).toList
      ys = xs.toSet.diff(vars)

      try {
        optionNormalizedEq = Some(ArithmeticNormalization(Minus(eq.left, eq.right), eqxs.toArray).toList)
      } catch {
        case ArithmeticNormalization.NonLinearExpressionException(_) =>
      }
    }

    optionNormalizedEq match {
      case None => RuleInapplicable
      case Some(normalizedEq0) => {
        val (neqxs, normalizedEq) = eqxs.zip(normalizedEq0.tail).filterNot{ case (_, IntLiteral(0)) => true case _ => false}.unzip

        //if(normalizedEq.size == 1) {


        //} else {

        val (eqPre, eqWitness, eqFreshVars) = elimVariable(eqas, normalizedEq)

        val eqSubstMap: Map[Expr, Expr] = neqxs.zip(eqWitness).map{case (id, e) => (Variable(id), simplify(e))}.toMap
        val freshFormula = simplify(replace(eqSubstMap, And(allOthers)))
        //}
        //(eqPre, freshFormula)

        val newProblem = Problem(as, And(eqPre, p.c), freshFormula, eqFreshVars)

        val onSuccess: List[Solution] => Solution = { 
          case List(Solution(pre, defs, term)) =>
            if (eqFreshVars.isEmpty) {
              Solution(pre, defs, replace(eqSubstMap, Tuple(neqxs.map(Variable(_)))))
            } else {
              Solution(pre, defs, LetTuple(eqFreshVars, term, replace(eqSubstMap, Tuple(neqxs.map(Variable(_))))))
            }
          case _ => Solution.none
        }

        RuleStep(List(newProblem), onSuccess)
      }
    }

  }
}
