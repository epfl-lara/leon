package leon
package synthesis

import purescala.Common._
import purescala.Trees._

object Rules {
  def all = List(
    OnePoint
  )
}


abstract class Rule(val name: String) {
  def isApplicable(p: Problem, parent: Task): List[Task]


  def subst(what: Tuple2[Identifier, Expr], in: Expr): Expr = replace(Map(Variable(what._1) -> what._2), in)
}

object OnePoint extends Rule("One-point") {
  def isApplicable(p: Problem, parent: Task): List[Task] = {

    p.phi match {
      case a : And =>
        def collectAnds(e: Expr): List[Expr] = e match {
          case And(exs) => exs.toList.flatMap(collectAnds)
          case e => List(e)
        }

        val exprs = collectAnds(a)
        val candidates = exprs.collect {
          case eq @ Equals(Variable(x), e) if (p.xs contains x) && !(variablesOf(e) contains x) =>
            (x, e, eq)
          case eq @ Equals(e, Variable(x)) if (p.xs contains x) && !(variablesOf(e) contains x) =>
            (x, e, eq)
        }

        if (!candidates.isEmpty) {
          val (x, e, eq) = candidates.head

          val others = exprs.filter(_ != eq)
          val oxs    = p.xs.filter(_ != x)

          val newProblem = Problem(p.as, subst(x -> e, And(others)), oxs)

          val onSuccess: List[Solution] => Solution = { 
            case List(Solution(pre, term)) =>
              if (oxs.isEmpty) {
                Solution(pre, e) 
              } else {
                Solution(pre, LetTuple(oxs, term, subst(x -> e, Tuple(p.xs.map(Variable(_))))) ) 
              }
            case _ => Solution.none
          }

          List(new Task(parent, p, List(newProblem), onSuccess, 100))
        } else {
          Nil
        }


      case _ =>
        Nil
    }
  }
}
