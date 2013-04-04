package leon
package synthesis

import purescala.Definitions.FunDef

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
                   rules: Seq[Rule],
                   costModel: CostModel) extends AndOrGraphSearch[TaskRunRule, TaskTryRules, Solution](new AndOrGraph(TaskTryRules(problem), SearchCostModel(costModel))) {

  def this(synth: Synthesizer, problem: Problem) = {
    this(synth, problem, synth.rules, synth.options.costModel)
  }

  import synth.reporter._

  val sctx = SynthesisContext.fromSynthesizer(synth)

  def expandAndTask(t: TaskRunRule): ExpandResult[TaskTryRules] = {
    val prefix = "[%-20s] ".format(Option(t.rule).getOrElse("?"))

    info(prefix+"Got: "+t.problem)
    t.app.apply(sctx) match {
      case RuleSuccess(sol, isTrusted) =>
        info(prefix+"Solved"+(if(isTrusted) "" else " (untrusted)")+" with: "+sol)

        ExpandSuccess(sol, isTrusted)
      case RuleDecomposed(sub) =>
        info(prefix+"Decomposed into:")
        for(p <- sub) {
          info(prefix+" - "+p)
        }

        Expanded(sub.map(TaskTryRules(_)))

      case RuleApplicationImpossible =>
        info(prefix+"Failed")

        ExpandFailure()
    }
  }

  def expandOrTask(t: TaskTryRules): ExpandResult[TaskRunRule] = {
    val (normRules, otherRules) = rules.partition(_.isInstanceOf[NormalizingRule])

    val normApplications = normRules.flatMap(_.instantiateOn(sctx, t.p))

    if (!normApplications.isEmpty) {
      Expanded(List(TaskRunRule(normApplications.head)))
    } else {
      val sub = otherRules.flatMap { r =>
        r.instantiateOn(sctx, t.p).map(TaskRunRule(_))
      }

      if (!sub.isEmpty) {
        Expanded(sub.toList)
      } else {
        ExpandFailure()
      }
    }
  }

  case class SubProgram(p: Problem, fd: FunDef, acc: Set[FunDef])

  def programAt(n: g.Tree): SubProgram = {
    import purescala.TypeTrees._
    import purescala.Common._
    import purescala.TreeOps.replace
    import purescala.Trees._
    import purescala.Definitions._

    def programFrom(from: g.AndNode, sp: SubProgram): SubProgram = {
      if (from.parent.parent eq null) {
        sp
      } else {
        val at = from.parent.parent
        val res = bestProgramForAnd(at, Map(from.parent -> sp))
        programFrom(at, res)
      }
    }

    def bestProgramForOr(on: g.OrTree): SubProgram = {
      val problem: Problem = on.task.p

      val fd = problemToFunDef(problem)

      SubProgram(problem, fd, Set(fd))
    }

    def fundefToSol(p: Problem, fd: FunDef): Solution = {
      Solution(BooleanLiteral(true), Set(), FunctionInvocation(fd, p.as.map(Variable(_))))
    }

    def solToSubProgram(p: Problem, s: Solution): SubProgram = {
      val fd = problemToFunDef(p)
      fd.precondition = Some(s.pre)
      fd.body         = Some(s.term)

      SubProgram(p, fd, Set(fd))
    }

    def bestProgramForAnd(an: g.AndNode, subPrograms: Map[g.OrTree, SubProgram]): SubProgram = {
      val subSubPrograms = an.subTasks.map(an.subProblems).map( ot =>
        subPrograms.getOrElse(ot, bestProgramForOr(ot))
      )

      val allFd = subSubPrograms.flatMap(_.acc)
      val subSolutions = subSubPrograms.map(ssp => fundefToSol(ssp.p, ssp.fd))

      val sp = solToSubProgram(an.task.problem, an.task.composeSolution(subSolutions).get)

      sp.copy(acc = sp.acc ++ allFd)
    }

    def problemToFunDef(p: Problem): FunDef = {

      val ret = if (p.xs.size == 1) {
        p.xs.head.getType
      } else {
        TupleType(p.xs.map(_.getType))
      }

      val freshAs = p.as.map(_.freshen)

      val map = (p.as.map(Variable(_): Expr) zip freshAs.map(Variable(_): Expr)).toMap

      val res = ResultVariable().setType(ret)

      val mapPost: Map[Expr, Expr] = if (p.xs.size > 1) {
        p.xs.zipWithIndex.map{ case (id, i)  =>
          Variable(id) -> TupleSelect(res, i+1)
        }.toMap
      } else {
        Map(Variable(p.xs.head) -> ResultVariable().setType(ret))
      }

      val fd = new FunDef(FreshIdentifier("chimp", true), ret, freshAs.map(id => VarDecl(id, id.getType)))
      fd.precondition = Some(replace(map, p.pc))
      fd.postcondition = Some(replace(map++mapPost, p.phi))

      fd
    }

    n match {
      case an: g.AndNode =>
        programFrom(an, bestProgramForAnd(an, Map.empty))

      case on: g.OrNode =>
        if (on.parent ne null) {
          programAt(on.parent)
        } else {
          bestProgramForOr(on)
        }
    }
  }


  var shouldStop = false

  def searchStep() {
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

  def search(): Option[(Solution, Boolean)] = {
    sctx.solver.init()

    shouldStop = false

    while (!g.tree.isSolved && !shouldStop) {
      searchStep()
    }
    g.tree.solution.map(s => (s, g.tree.isTrustworthy))
  }

  override def stop() {
    super.stop()
    shouldStop = true
    sctx.solver.halt()
  }
}
