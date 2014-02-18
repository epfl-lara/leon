package leon
package termination

import purescala.Definitions._
import purescala.Trees._
import purescala.TreeOps._

class LoopProcessor(checker: TerminationChecker,
                    chainBuilder: ChainBuilder,
                    val structuralSize: StructuralSize,
                    val strengthener: Strengthener,
                    k: Int = 10) extends Processor(checker) with Solvable {

  val name: String = "Loop Processor"

  def run(problem: Problem) = {
    val allChains : Set[Chain] = problem.funDefs.map(fd => chainBuilder.run(fd)).flatten
    // Get reentrant loops (see ChainProcessor for more details)
    val chains    : Set[Chain] = allChains.filter(chain => isWeakSAT(And(chain reentrant chain)))

    val nonTerminating = chains.flatMap({ chain =>
      val freshArgs : Seq[Expr] = chain.funDef.params.map(arg => arg.id.freshen.toVariable)
      val finalBindings = (chain.funDef.params.map(_.id) zip freshArgs).toMap
      val path = chain.loop(finalSubst = finalBindings)
      val formula = And(path :+ Equals(Tuple(chain.funDef.params.map(_.toVariable)), Tuple(freshArgs)))

      val solvable = functionCallsOf(formula).forall({
        case FunctionInvocation(tfd, args) => checker.terminates(tfd.fd).isGuaranteed
      })

      if (!solvable) None else getModel(formula) match {
        case Some(map) => Some(chain.funDef -> chain.funDef.params.map(arg => map(arg.id)))
        case _ => None
      }
    }).toMap

    val results = nonTerminating.map({ case (funDef, args) => Broken(funDef, args) })
    val remaining = problem.funDefs -- nonTerminating.keys
    val newProblems = if (remaining.nonEmpty) List(Problem(remaining)) else Nil
    (results, newProblems)
  }
}

// vim: set ts=4 sw=4 et:
