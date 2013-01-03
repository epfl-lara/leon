package leon
package synthesis

import synthesis.search._

case class TaskRunRule(app: RuleInstantiation) extends AOAndTask[Solution] {

  val problem = app.problem
  val rule    = app.rule

  def composeSolution(sols: List[Solution]): Option[Solution] = {
    app.onSuccess(sols)
  }

  override def toString = rule.name
}

case class TaskTryRules(p: Problem) extends AOOrTask[Solution] {
  override def toString = p.toString
}

case class SearchCostModel(cm: CostModel) extends AOCostModel[TaskRunRule, TaskTryRules, Solution] {
  def taskCost(t: AOTask[Solution]) = t match {
    case ttr: TaskRunRule =>
      cm.ruleAppCost(ttr.app)
    case trr: TaskTryRules =>
      cm.problemCost(trr.p)
  }

  def solutionCost(s: Solution) = cm.solutionCost(s)
}

class SimpleSearch(synth: Synthesizer,
                   problem: Problem,
                   rules: Set[Rule],
                   costModel: CostModel) extends AndOrGraphSearch[TaskRunRule, TaskTryRules, Solution](new AndOrGraph(TaskTryRules(problem), SearchCostModel(costModel))) {

  import synth.reporter._

  val sctx = SynthesisContext.fromSynthesizer(synth)

  def expandAndTask(t: TaskRunRule): ExpandResult[TaskTryRules] = {
    val prefix = "[%-20s] ".format(Option(t.rule).getOrElse("?"))

    t.app.apply(sctx) match {
      case RuleSuccess(sol) =>
        info(prefix+"Got: "+t.problem)
        info(prefix+"Solved with: "+sol)

        ExpandSuccess(sol)
      case RuleDecomposed(sub) =>
        info(prefix+"Got: "+t.problem)
        info(prefix+"Decomposed into:")
        for(p <- sub) {
          info(prefix+" - "+p)
        }

        Expanded(sub.map(TaskTryRules(_)))

      case RuleApplicationImpossible =>
        ExpandFailure()
    }
  }

  def expandOrTask(t: TaskTryRules): ExpandResult[TaskRunRule] = {
    val sub = rules.flatMap ( r => r.instantiateOn(sctx, t.p).map(TaskRunRule(_)) )

    if (!sub.isEmpty) {
      Expanded(sub.toList)
    } else {
      ExpandFailure()
    }
  }

  var shouldStop = false

  def search(): Option[Solution] = {
    sctx.solver.init()

    shouldStop = false

    while (!g.tree.isSolved && !shouldStop) {
      nextLeaf() match {
        case Some(l)  =>
          l match {
            case al: g.AndLeaf =>
              val sub = expandAndTask(al.task)
              onExpansion(al, sub)
            case ol: g.OrLeaf =>
              val sub = expandOrTask(ol.task)
              onExpansion(ol, sub)
          }
        case None =>
          stop()
      }
    }
    g.tree.solution
  }

  override def stop() {
    super.stop()
    shouldStop = true
    sctx.solver.halt()
  }
}
