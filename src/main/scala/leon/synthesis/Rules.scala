package leon
package synthesis

import purescala.Common._
import purescala.Trees._
import purescala.TypeTrees._

object Rules {
  def all(synth: Synthesizer) = List(
    new OnePoint(synth),
    new Ground(synth)
  )
}


abstract class Rule(val name: String, val synth: Synthesizer) {
  def isApplicable(p: Problem, parent: Task): List[Task]

  def subst(what: Tuple2[Identifier, Expr], in: Expr): Expr = replace(Map(Variable(what._1) -> what._2), in)

  override def toString = name
}

class OnePoint(synth: Synthesizer) extends Rule("One-point", synth) {
  def isApplicable(p: Problem, parent: Task): List[Task] = {

    p.phi match {
      case TopLevelAnds(exprs) =>
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

          List(new Task(synth, parent, this, p, List(newProblem), onSuccess, 100))
        } else {
          Nil
        }


      case _ =>
        Nil
    }
  }
}

class Ground(synth: Synthesizer) extends Rule("Ground", synth) {
  def isApplicable(p: Problem, parent: Task): List[Task] = {
    if (p.as.isEmpty) {

      val tpe = TupleType(p.xs.map(_.getType))

      synth.solveSAT(p.phi) match {
        case (Some(true), model) =>
          val onSuccess: List[Solution] => Solution = { 
            case Nil => Solution(BooleanLiteral(true), Tuple(p.xs.map(model)).setType(tpe))
          }

          List(new Task(synth, parent, this, p, Nil, onSuccess, 200))
        case (Some(false), model) =>
          val onSuccess: List[Solution] => Solution = { 
            case Nil => Solution(BooleanLiteral(false), Error(p.phi+" is UNSAT!").setType(tpe))
          }

          List(new Task(synth, parent, this, p, Nil, onSuccess, 200))
        case _ =>
          Nil
      }
    } else {
      Nil
    }
  }
}
