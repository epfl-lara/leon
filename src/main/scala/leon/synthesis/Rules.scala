package leon
package synthesis

import purescala.Common._
import purescala.ScalaPrinter
import purescala.Trees._
import purescala.Extractors._
import purescala.TreeOps._
import purescala.TypeTrees._

object Rules {
  def all(synth: Synthesizer) = Set(
    new Unification.DecompTrivialClash(synth),
    new Unification.OccursCheck(synth),
    new ADTDual(synth),
    new OnePoint(synth),
    new Ground(synth),
    new CaseSplit(synth),
    new UnusedInput(synth),
    new UnconstrainedOutput(synth),
    new Assert(synth)
  )
}

abstract class RuleResult
case object RuleInapplicable extends RuleResult
case class RuleSuccess(solution: Solution) extends RuleResult
case class RuleDecomposed(subProblems: List[Problem], onSuccess: List[Solution] => Solution) extends RuleResult


abstract class Rule(val name: String, val synth: Synthesizer, val priority: Priority) {
  def applyOn(task: Task): RuleResult

  def subst(what: Tuple2[Identifier, Expr], in: Expr): Expr = replace(Map(Variable(what._1) -> what._2), in)
  def substAll(what: Map[Identifier, Expr], in: Expr): Expr = replace(what.map(w => Variable(w._1) -> w._2), in)

  val forward: List[Solution] => Solution = {
    case List(s) => Solution(s.pre, s.term)
    case _ => Solution.none
  }

  override def toString = name
}

class OnePoint(synth: Synthesizer) extends Rule("One-point", synth, 30) {
  def applyOn(task: Task): RuleResult = {

    val p = task.problem

    val TopLevelAnds(exprs) = p.phi

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
            Solution(pre, Tuple(e :: Nil)) 
          } else {
            Solution(pre, LetTuple(oxs, term, subst(x -> e, Tuple(p.xs.map(Variable(_)))))) 
          }
        case _ => Solution.none
      }

      RuleDecomposed(List(newProblem), onSuccess)
    } else {
      RuleInapplicable
    }
  }
}

class Ground(synth: Synthesizer) extends Rule("Ground", synth, 50) {
  def applyOn(task: Task): RuleResult = {
    val p = task.problem

    if (p.as.isEmpty) {

      val tpe = TupleType(p.xs.map(_.getType))

      synth.solver.solveSAT(p.phi) match {
        case (Some(true), model) =>
          RuleSuccess(Solution(BooleanLiteral(true), Tuple(p.xs.map(valuateWithModel(model))).setType(tpe)))
        case (Some(false), model) =>
          RuleSuccess(Solution(BooleanLiteral(false), Error(p.phi+" is UNSAT!").setType(tpe)))
        case _ =>
          RuleInapplicable
      }
    } else {
      RuleInapplicable
    }
  }
}

class CaseSplit(synth: Synthesizer) extends Rule("Case-Split", synth, 20) {
  def applyOn(task: Task): RuleResult = {
    val p = task.problem
    p.phi match {
      case Or(Seq(o1, o2)) =>
        val sub1 = Problem(p.as, o1, p.xs)
        val sub2 = Problem(p.as, o2, p.xs)

        val onSuccess: List[Solution] => Solution = { 
          case List(Solution(p1, t1), Solution(p2, t2)) => Solution(Or(p1, p2), IfExpr(p1, t1, t2))
          case _ => Solution.none
        }

        RuleDecomposed(List(sub1, sub2), onSuccess)
      case _ =>
        RuleInapplicable
    }
  }
}

class Assert(synth: Synthesizer) extends Rule("Assert", synth, 20) {
  def applyOn(task: Task): RuleResult = {
    val p = task.problem

    p.phi match {
      case TopLevelAnds(exprs) =>
        val xsSet = p.xs.toSet

        val (exprsA, others) = exprs.partition(e => (variablesOf(e) & xsSet).isEmpty)

        if (!exprsA.isEmpty) {
          if (others.isEmpty) {
            RuleSuccess(Solution(And(exprsA), Tuple(p.xs.map(id => simplestValue(Variable(id))))))
          } else {
            /*
             * Disable for now, it is not that useful anyway
            val onSuccess: List[Solution] => Solution = { 
              case List(s) => Solution(And(s.pre +: exprsA), s.term)
              case _ => Solution.none
            }

            val sub = p.copy(phi = And(others))

            RuleDecomposed(List(sub), onSuccess)
            */
            RuleInapplicable
          }
        } else {
          RuleInapplicable
        }
      case _ =>
        RuleInapplicable
    }
  }
}

class UnusedInput(synth: Synthesizer) extends Rule("UnusedInput", synth, 10) {
  def applyOn(task: Task): RuleResult = {
    val p = task.problem
    val unused = p.as.toSet -- variablesOf(p.phi)

    if (!unused.isEmpty) {
      val sub = p.copy(as = p.as.filterNot(unused))

      RuleDecomposed(List(sub), forward)
    } else {
      RuleInapplicable
    }
  }
}

class UnconstrainedOutput(synth: Synthesizer) extends Rule("Unconstr.Output", synth, 10) {
  def applyOn(task: Task): RuleResult = {
    val p = task.problem
    val unconstr = p.xs.toSet -- variablesOf(p.phi)

    if (!unconstr.isEmpty) {
      val sub = p.copy(xs = p.xs.filterNot(unconstr))

      val onSuccess: List[Solution] => Solution = { 
        case List(s) => 
          Solution(s.pre, LetTuple(sub.xs, s.term, Tuple(p.xs.map(id => if (unconstr(id)) simplestValue(Variable(id)) else Variable(id)))))
        case _ =>
          Solution.none
      }

      RuleDecomposed(List(sub), onSuccess)
    } else {
      RuleInapplicable
    }

  }
}

object Unification {
  class DecompTrivialClash(synth: Synthesizer) extends Rule("Unif Dec./Clash/Triv.", synth, 20) {
    def applyOn(task: Task): RuleResult = {
      val p = task.problem

      val TopLevelAnds(exprs) = p.phi

      val (toRemove, toAdd) = exprs.collect {
        case eq @ Equals(cc1 @ CaseClass(cd1, args1), cc2 @ CaseClass(cd2, args2)) =>
          if (cc1 == cc2) {
            (eq, List(BooleanLiteral(true)))
          } else if (cd1 == cd2) {
            (eq, (args1 zip args2).map((Equals(_, _)).tupled))
          } else {
            (eq, List(BooleanLiteral(false)))
          }
      }.unzip

      if (!toRemove.isEmpty) {
        val sub = p.copy(phi = And((exprs.toSet -- toRemove ++ toAdd.flatten).toSeq))


        RuleDecomposed(List(sub), forward)
      } else {
        RuleInapplicable
      }
    }
  }

  class OccursCheck(synth: Synthesizer) extends Rule("Unif OccursCheck", synth, 20) {
    def applyOn(task: Task): RuleResult = {
      val p = task.problem

      val TopLevelAnds(exprs) = p.phi

      val isImpossible = exprs.exists {
        case eq @ Equals(cc : CaseClass, Variable(id)) if variablesOf(cc) contains id =>
          true
        case eq @ Equals(Variable(id), cc : CaseClass) if variablesOf(cc) contains id =>
          true
        case _ =>
          false
      }

      if (isImpossible) {
        val tpe = TupleType(p.xs.map(_.getType))

        RuleSuccess(Solution(BooleanLiteral(false), Error(p.phi+" is UNSAT!").setType(tpe)))
      } else {
        RuleInapplicable
      }
    }
  }
}


class ADTDual(synth: Synthesizer) extends Rule("ADTDual", synth, 20) {
  def applyOn(task: Task): RuleResult = {
    val p = task.problem

    val xs = p.xs.toSet
    val as = p.as.toSet

    val TopLevelAnds(exprs) = p.phi


    val (toRemove, toAdd) = exprs.collect {
      case eq @ Equals(cc @ CaseClass(cd, args), e) if (variablesOf(e) -- as).isEmpty && (variablesOf(cc) -- xs).isEmpty =>
        (eq, CaseClassInstanceOf(cd, e) +: (cd.fieldsIds zip args).map{ case (id, ex) => Equals(ex, CaseClassSelector(cd, e, id)) } )
      case eq @ Equals(e, cc @ CaseClass(cd, args)) if (variablesOf(e) -- as).isEmpty && (variablesOf(cc) -- xs).isEmpty =>
        (eq, CaseClassInstanceOf(cd, e) +: (cd.fieldsIds zip args).map{ case (id, ex) => Equals(ex, CaseClassSelector(cd, e, id)) } )
    }.unzip

    if (!toRemove.isEmpty) {
      val sub = p.copy(phi = And((exprs.toSet -- toRemove ++ toAdd.flatten).toSeq))

      RuleDecomposed(List(sub), forward)
    } else {
      RuleInapplicable
    }
  }
}

