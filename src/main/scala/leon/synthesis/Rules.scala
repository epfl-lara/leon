package leon
package synthesis

import purescala.Trees._

object Rules {
  def all = List(
    OnePoint
  )
}


abstract class Rule(val name: String) {
  def isApplicable(p: Problem, parent: Task): List[Task]
}

object OnePoint extends Rule("One-point") {
  def isApplicable(p: Problem, parent: Task): List[Task] = {

    p.phi match {
      case And(exprs) =>
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

          val newProblem = Problem(p.as, replace(Map(Variable(x) -> e), And(others)), oxs)

          val onSuccess: List[Solution] => Solution = { 
            case List(Solution(pre, term)) =>
              if (oxs.isEmpty) {
                Solution(pre, e) 
              } else {
                Solution(pre, LetTuple(oxs, term, replace(Map(Variable(x) -> e), Tuple(p.xs.map(Variable(_))))) ) 
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
