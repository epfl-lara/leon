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

class IntegerInequality(synth: Synthesizer) extends Rule("Integer Inequality", synth, 300) {
  def applyOn(task: Task): RuleResult = {

    val problem = task.problem
    val TopLevelAnds(exprs) = problem.phi

    //assume that we only have inequalities
    var nonIneq = false

    //normalized all inequalities to LessEquals(t, 0)
    val lhsSides: List[Expr] = exprs.map{
      case LessThan(a, b) => Plus(Minus(a, b), IntLiteral(1))
      case LessEquals(a, b) => Minus(a, b)
      case GreaterThan(a, b) => Plus(Minus(b, a), IntLiteral(1))
      case GreaterEquals(a, b) => Minus(b, a)
      case _ => {nonIneq = true; null}
    }.toList

    if(nonIneq) RuleInapplicable else {
      var processedVar: Option[Identifier] = None
      for(e <- lhsSides if processedVar == None) {
        val vars = variablesOf(e)
        if(!vars.isEmpty)
          processedVar = Some(vars.head)
      }
      processedVar match {
        case None => RuleInapplicable 
        case Some(processedVar) => {
          val normalizedLhs: List[List[Expr]] = lhsSides.map(ArithmeticNormalization(_, Array(processedVar)).toList)
          var upperBounds: List[(Expr, Int)] = Nil // (t, c) means c*x <= t
          var lowerBounds: List[(Expr, Int)] = Nil // (t, c) means t <= c*x
          normalizedLhs.foreach{
            case List(t, IntLiteral(i)) => 
              if(i > 0) upperBounds ::= (simplify(UMinus(t)), i)
              else if(i < 0) lowerBounds ::= (simplify(t), -i)
            case err => sys.error("unexpected from normal form: " + err)
          }
          println("processed var: " + processedVar)
          println("upperBounds: " + upperBounds)
          println("lowerBounds: " + lowerBounds)

          val L = GCD.lcm((upperBounds ::: lowerBounds).map(_._2))
          val newUpperBounds: List[Expr] = upperBounds.map{case (bound, coef) => Times(IntLiteral(L/coef), bound)}
          val newLowerBounds: List[Expr] = lowerBounds.map{case (bound, coef) => Times(IntLiteral(L/coef), bound)}
          println("newupperBounds: " + newUpperBounds)
          println("newLowerBounds: " + newLowerBounds)


          val remainderIds: List[Identifier] = newUpperBounds.map(_ => FreshIdentifier("k", true).setType(Int32Type))
          val quotientIds: List[Identifier] = newUpperBounds.map(_ => FreshIdentifier("l", true).setType(Int32Type))

          val subProblemFormula = simplify(And(
            newUpperBounds.zip(remainderIds).zip(quotientIds).flatMap{
              case ((b, k), l) => Equals(b, Plus(Times(IntLiteral(L), Variable(l)), Variable(k))) :: 
                                  newLowerBounds.map(lbound => LessEquals(Variable(k), Minus(b, lbound)))
            }))
          println("subform: " + subProblemFormula)

          val otherVars: List[Identifier] = problem.xs.filterNot(_ == processedVar)
          val subProblem = Problem(problem.as ++ remainderIds, problem.c, subProblemFormula, otherVars ++ quotientIds) 

          def onSuccess(sols: List[Solution]): Solution = sols match {
            case List(Solution(pre, defs, term)) => {
              if(newUpperBounds.isEmpty) {
                Solution(pre, defs,
                  LetTuple(otherVars++quotientIds, term,
                    Let(processedVar, newLowerBounds.head, Tuple(problem.xs.map(Variable(_))))))
              } else if(newLowerBounds.isEmpty) {
                Solution(pre, defs,
                  LetTuple(otherVars++quotientIds, term,
                    Let(processedVar, newUpperBounds.head, Tuple(problem.xs.map(Variable(_))))))
              } else if(newUpperBounds.size > 1)
                Solution.none
              else {
                val k = remainderIds.head
                
                val loopCounter = Variable(FreshIdentifier("i").setType(Int32Type))
                val concretePre = replace(Map(Variable(k) -> loopCounter), pre)
                val returnType = TupleType(problem.xs.map(_.getType))
                val funDef = new FunDef(FreshIdentifier("rec", true), returnType, Seq(VarDecl(loopCounter.id, Int32Type)))
                val funBody = IfExpr(
                  LessThan(loopCounter, IntLiteral(0)),
                  Error("No solution exists"),
                  IfExpr(
                    concretePre,
                    LetTuple(otherVars++quotientIds, term,
                      Let(processedVar, 
                          if(newUpperBounds.isEmpty) newLowerBounds.head else newUpperBounds.head, 
                          Tuple(problem.xs.map(Variable(_))))
                    ),
                    FunctionInvocation(funDef, Seq(Minus(loopCounter, IntLiteral(1))))
                  )
                )
                funDef.body = Some(funBody)

                println("generated code: " + funDef)

                Solution(pre, defs + funDef, FunctionInvocation(funDef, Seq(IntLiteral(L-1))))
              }
            }
            case _ => Solution.none
          }

          RuleStep(List(subProblem), onSuccess)
        }
      }
    }
  }
}
