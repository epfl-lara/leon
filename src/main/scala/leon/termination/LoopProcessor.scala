package leon
package termination

import purescala.Definitions._
import purescala.Trees._
import purescala.TreeOps._

import scala.collection.mutable.{Map => MutableMap}

class LoopProcessor(val checker: TerminationChecker with ChainBuilder with Strengthener with StructuralSize) extends Processor with Solvable {

  val name: String = "Loop Processor"

  def run(problem: Problem) = {
    reporter.debug("- Strengthening applications")
    checker.strengthenApplications(problem.funDefs)(this)

    reporter.debug("- Running ChainBuilder")
    val allChains : Set[Chain] = problem.funDefs.map(fd => checker.getChains(fd)(this)).flatten

    // Get reentrant loops (see ChainProcessor for more details)
    val chains    : Set[Chain] = allChains.filter(chain => maybeSAT(And(chain reentrant chain), chain.funDef.precondition))

    reporter.debug("- Searching for loops")
    val nonTerminating: MutableMap[FunDef, (Seq[Expr], Boolean)] = MutableMap.empty
    for (chain <- chains if !nonTerminating.contains(chain.funDef)) {
      val freshArgs : Seq[Expr] = chain.funDef.args.map(arg => arg.id.freshen.toVariable)
      val finalBindings = (chain.funDef.args.map(_.id) zip freshArgs).toMap
      val path = chain.loop(finalSubst = finalBindings)
      val formula = And(path :+ Equals(Tuple(chain.funDef.args.map(_.toVariable)), Tuple(freshArgs)))

      definitiveSATwithModel(formula, chain.funDef.precondition) foreach { map =>
        nonTerminating(chain.funDef) = (chain.funDef.args.map(arg => map(arg.id)), chain.chain.exists(_.inAnon))
      }
    }

    val results = nonTerminating.map({
      case (funDef, (args, inAnon)) => if (inAnon) MaybeBroken(funDef, args) else Broken(funDef, args)
    })

    val remaining = problem.funDefs -- nonTerminating.keys
    val newProblems = if (remaining.nonEmpty) List(Problem(remaining)) else Nil
    (results, newProblems)
  }
}

// vim: set ts=4 sw=4 et:
