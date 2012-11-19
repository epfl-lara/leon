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
  def attemptToApplyOn(problem: Problem): RuleResult = {

    val TopLevelAnds(exprs) = problem.phi

    val (eqs, others) = exprs.partition(_.isInstanceOf[Equals])
    var candidates: Seq[Expr] = eqs
    var allOthers: Seq[Expr] = others

    var vars: Set[Identifier] = Set()
    var eqxs: List[Identifier] = List()

    var optionNormalizedEq: Option[List[Expr]] = None
    while(!candidates.isEmpty && optionNormalizedEq == None) {
      val eq@Equals(_,_) = candidates.head
      candidates = candidates.tail
      
      vars = variablesOf(eq)
      eqxs = problem.xs.toSet.intersect(vars).toList

      try {
        optionNormalizedEq = Some(ArithmeticNormalization(Minus(eq.left, eq.right), eqxs.toArray).toList)
      } catch {
        case ArithmeticNormalization.NonLinearExpressionException(_) =>
          allOthers = allOthers :+ eq
      }
    }
    allOthers = allOthers ++ candidates

    optionNormalizedEq match {
      case None => RuleInapplicable
      case Some(normalizedEq0) => {

        val eqas = problem.as.toSet.intersect(vars)

        val (neqxs, normalizedEq1) = eqxs.zip(normalizedEq0.tail).filterNot{ case (_, IntLiteral(0)) => true case _ => false}.unzip
        val normalizedEq = normalizedEq0.head :: normalizedEq1

        if(normalizedEq.size == 1) {
          val eqPre = Equals(normalizedEq.head, IntLiteral(0))
          val newProblem = Problem(problem.as, And(eqPre, problem.c), And(allOthers), problem.xs)

          val onSuccess: List[Solution] => Solution = { 
            case List(Solution(pre, defs, term)) => {
              Solution(And(eqPre, pre), defs, term)
            }
            case _ => Solution.none
          }

          RuleFastStep(List(newProblem), onSuccess)

        } else {
          val (eqPre0, eqWitness, freshxs) = elimVariable(eqas, normalizedEq)
          val eqPre = eqPre0 match {
            case Equals(Modulo(_, IntLiteral(1)), _) => BooleanLiteral(true)
            case c => c
          }

          val eqSubstMap: Map[Expr, Expr] = neqxs.zip(eqWitness).map{case (id, e) => (Variable(id), simplify(e))}.toMap
          val freshFormula0 = simplify(replace(eqSubstMap, And(allOthers)))

          var freshInputVariables: List[Identifier] = Nil
          var equivalenceConstraints: Map[Expr, Expr] = Map()
          val freshFormula = simplePreTransform({
            case d@Division(_, _) => {
              assert(variablesOf(d).intersect(problem.xs.toSet).isEmpty)
              val newVar = FreshIdentifier("d", true).setType(Int32Type) 
              freshInputVariables ::= newVar
              equivalenceConstraints += (Variable(newVar) -> d)
              Variable(newVar)
            }
            case e => e
          })(freshFormula0)

          val ys: List[Identifier] = problem.xs.filterNot(neqxs.contains(_))
          val subproblemxs: List[Identifier] = freshxs ++ ys

          val newProblem = Problem(problem.as ++ freshInputVariables, And(eqPre, problem.c), freshFormula, subproblemxs)

          val onSuccess: List[Solution] => Solution = { 
            case List(Solution(pre, defs, term)) => {
              val freshPre = replace(equivalenceConstraints, pre)
              val freshTerm = replace(equivalenceConstraints, term)
              val freshsubxs = subproblemxs.map(id => FreshIdentifier(id.name).setType(id.getType))
              val id2res: Map[Expr, Expr] = 
                freshsubxs.zip(subproblemxs).map{case (id1, id2) => (Variable(id1), Variable(id2))}.toMap ++
                neqxs.map(id => (Variable(id), eqSubstMap(Variable(id)))).toMap
              Solution(And(eqPre, freshPre), defs, simplify(simplifyLets(LetTuple(subproblemxs, freshTerm, replace(id2res, Tuple(problem.xs.map(Variable(_))))))))
            }
            case _ => Solution.none
          }

          RuleFastStep(List(newProblem), onSuccess)
        }


      }
    }

  }
}
