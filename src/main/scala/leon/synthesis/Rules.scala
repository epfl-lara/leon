package leon
package synthesis

import purescala.Common._
import purescala.Trees._
import purescala.TypeTrees._

object Rules {
  def all(synth: Synthesizer) = List(
    new OnePoint(synth),
    new Ground(synth),
    new CaseSplit(synth),
    new UnusedInput(synth),
    new Assert(synth)
  )
}


abstract class Rule(val name: String, val synth: Synthesizer) {
  def isApplicable(task: Task): List[DecomposedTask]

  def subst(what: Tuple2[Identifier, Expr], in: Expr): Expr = replace(Map(Variable(what._1) -> what._2), in)

  override def toString = name
}

class OnePoint(synth: Synthesizer) extends Rule("One-point", synth) {
  def isApplicable(task: Task): List[DecomposedTask] = {

    val p = task.problem

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
            case List(Solution(pre, term, sc)) =>
              if (oxs.isEmpty) {
                Solution(pre, e, sc) 
              } else {
                Solution(pre, LetTuple(oxs, term, subst(x -> e, Tuple(p.xs.map(Variable(_))))), sc) 
              }
            case _ => Solution.none
          }

          List(task.decompose(this, List(newProblem), onSuccess, 100))
        } else {
          Nil
        }


      case _ =>
        Nil
    }
  }
}

class Ground(synth: Synthesizer) extends Rule("Ground", synth) {
  def isApplicable(task: Task): List[DecomposedTask] = {
    val p = task.problem

    if (p.as.isEmpty) {

      val tpe = TupleType(p.xs.map(_.getType))

      synth.solveSAT(p.phi) match {
        case (Some(true), model) =>
          List(task.solveUsing(this, Solution(BooleanLiteral(true), Tuple(p.xs.map(model)).setType(tpe), 200), 200))
        case (Some(false), model) =>
          List(task.solveUsing(this, Solution(BooleanLiteral(false), Error(p.phi+" is UNSAT!").setType(tpe), 200), 200))
        case _ =>
          Nil
      }
    } else {
      Nil
    }
  }
}

class CaseSplit(synth: Synthesizer) extends Rule("Case-Split", synth) {
  def isApplicable(task: Task): List[DecomposedTask] = {
    val p = task.problem
    p.phi match {
      case Or(Seq(o1, o2)) =>
        val sub1 = Problem(p.as, o1, p.xs)
        val sub2 = Problem(p.as, o2, p.xs)

        val onSuccess: List[Solution] => Solution = { 
          case List(s1, s2) => Solution(Or(s1.pre, s2.pre), IfExpr(s1.pre, s1.term, s2.term), 100)
          case _ => Solution.none
        }

        List(task.decompose(this, List(sub1, sub2), onSuccess, 100))
      case _ =>
        Nil
    }
  }
}

class Assert(synth: Synthesizer) extends Rule("Assert", synth) {
  def isApplicable(task: Task): List[DecomposedTask] = {
    val p = task.problem

    p.phi match {
      case TopLevelAnds(exprs) =>
        val xsSet = p.xs.toSet

        val (exprsA, others) = exprs.partition(e => (variablesOf(e) & xsSet).isEmpty)

        if (!exprsA.isEmpty) {
          if (others.isEmpty) {
            List(task.solveUsing(this, Solution(And(exprsA), BooleanLiteral(true), 150), 150))
          } else {
            val onSuccess: List[Solution] => Solution = { 
              case List(s) => Solution(And(s.pre +: exprsA), s.term, 150)
              case _ => Solution.none
            }

            val sub = p.copy(phi = And(others))

            List(task.decompose(this, List(sub), onSuccess, 150))
          }
        } else {
          Nil
        }
      case _ =>
        Nil
    }
  }
}

class UnusedInput(synth: Synthesizer) extends Rule("UnusedInput", synth) {
  def isApplicable(task: Task): List[DecomposedTask] = {
    val p = task.problem
    val unused = p.as.toSet -- variablesOf(p.phi)

    if (!unused.isEmpty) {
        val sub = p.copy(as = p.as.filterNot(unused))

        val onSuccess: List[Solution] => Solution = { 
          case List(s) => s
          case _ => Solution.none
        }

        List(task.decompose(this, List(sub), onSuccess, 300))
    } else {
      Nil
    }
  }
}
