/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package synthesis
package rules

import purescala.Expressions._
import purescala.Common._
import purescala.Definitions._
import purescala.Types._
import purescala.ExprOps._
import purescala.TypeOps.depth
import purescala.DefOps._
import purescala.Constructors._
import collection.mutable.ArrayBuffer

import utils.MutableExpr
import solvers._
import leon.grammars._
import leon.grammars.aspects._
import leon.utils._

import evaluators._
import datagen._

import scala.collection.mutable.{HashMap => MutableMap}

abstract class STELike(name: String) extends Rule(name) {

  class NonDeterministicProgram(
    interruptManager: InterruptManager,
    outerCtx: SearchContext,
    outerP: Problem,
    initSize: Int,
    outerExamples: Seq[Example]
  ) {
    type Candidate = Set[Identifier]

    import outerCtx.reporter._

    // Track non-deterministic candidates up to 100'000 expressions, or give up
    val nCandidatesLimit = 100000

    // The factor by which programs need to be reduced by testing before we validate them individually
    val testReductionRatio = 10

    // Timeout to find a candidate program
    val exSolverTo  = 500L

    // Timeout to find a counter example to a candidate program
    val cexSolverTo = 3000L

    val timers = outerCtx.timers.synthesis.applications.STE

    // STE Flags to activate or deactivate features
    val useOptTimeout = outerCtx.settings.steUseOptTimeout
    val useVanuatoo   = outerCtx.settings.steUseVanuatoo


    // Create a fresh solution function with the best solution around the
    // current STE as body
    val fd = {
      val fd = outerCtx.functionContext.duplicate()

      fd.fullBody = postMap {
        case src if src eq outerCtx.source =>
          val body = new PartialSolution(outerCtx.search.strat, true)(outerCtx)
                      .solutionAround(outerCtx.currentNode)(MutableExpr(NoTree(outerP.outType)))
                      .getOrElse(fatalError("Unable to get outer solution"))
                      .term

          Some(body)
        case _ =>
          None
      } (fd.fullBody)

      fd
    }

    // Create a program replacing the synthesis source by the fresh solution
    // function
    val (outerToInner, innerToOuter, solutionBox, program) = {
      val t = funDefReplacer {
        case fd2 if fd2 == outerCtx.functionContext =>
          Some(fd)

        case fd2 =>
          Some(fd2.duplicate())
      }

      val innerProgram = transformProgram(t, outerCtx.program)

      val solutionBox = collect[MutableExpr] {
        case me: MutableExpr => Set(me)
        case _ => Set()
      }(fd.fullBody).head

      (t, t.inverse, solutionBox, innerProgram)
    }

    // It should be set to the solution you want to check at each time.
    // Usually it will either be cExpr or a concrete solution.
    private def setSolution(e: Expr) = solutionBox.underlying = e

    implicit val sctx = new SynthesisContext(outerCtx, outerCtx.settings, fd, program)

    val p = {
      implicit val bindings = Map[Identifier, Identifier]()

      Problem(
        as  = outerP.as.map(outerToInner.transform),
        ws  = outerToInner.transform(outerP.ws),
        pc  = outerP.pc.map(outerToInner.transform),
        phi = outerToInner.transform(outerP.phi),
        xs  = outerP.xs.map(outerToInner.transform)
      )
    }

    private val spec = letTuple(p.xs, solutionBox, p.phi)

    val params = getParams(sctx, p)

    val evaluator = new DefaultEvaluator(sctx, program)

    // Current synthesized term size
    private var termSize_ = 0

    def termSize = termSize_

    private val grammar = params.grammar

    def rootLabel = {
      val targetType = tupleTypeWrap(p.xs.map(_.getType))

      params.rootLabel(targetType)
        .withAspect(TypeDepthBound(depth(targetType) + 1))
        .withAspect(Sized(termSize, params.optimizations))
    }


    val cexSolverF = SolverFactory.getFromSettings(sctx, program).withTimeout(cexSolverTo)
    val exSolverF  = SolverFactory.getFromSettings(sctx, program).withTimeout(exSolverTo)

    /**
     * We (lazily) generate additional tests for discarding potential programs with a data generator
     */
    val innerExamplesGenerator: Iterator[Example] = {
      val nTests = if (p.pc.isEmpty) 50 else 20

      val complicated = exists {
        case FunctionInvocation(tfd, _) if tfd.fd == fd => true
        case Choose(_) => true
        case _ => false
      }(p.pc.toClause)

      if (complicated) {
        Iterator()
      } else {
        if (useVanuatoo) {
          new VanuatooDataGen(sctx, program).generateFor(p.as, p.pc.toClause, nTests, 3000).map(InExample)
        } else {
          new GrammarDataGen(evaluator, ValueGrammar).generateFor(p.as, p.pc.toClause, nTests, 1000).map(InExample)
        }
      }
    }

    /**
     * Different view of the tree of expressions:
     *
     * Case used to illustrate the different views, assuming encoding:
     *
     *   b1 => c1 == F(c2, c3)
     *   b2 => c1 == G(c4, c5)
     *   b3 => c6 == H(c4, c5)
     *
     * c1 -> Seq(
     *         (b1, F(_, _), Seq(c2, c3))
     *         (b2, G(_, _), Seq(c4, c5))
     *       )
     * c6 -> Seq(
     *         (b3, H(_, _), Seq(c7, c8))
     *       )
     */
    private var cTree: Map[Identifier, Seq[(Identifier, Seq[Expr] => Expr, Seq[Identifier])]] = Map()

    // cTree in expression form
    private var cExpr: Expr = _

    // Top-level C identifiers corresponding to innerP.xs
    private var rootC: Identifier          = _

    // Blockers
    private var bs: Set[Identifier]        = Set()

    private var bsOrdered: Seq[Identifier] = Seq()

    // Generator of fresh cs that minimizes labels
    class CGenerator {
      private var buffers = Map[Label, Stream[Identifier]]()

      private var slots = Map[Label, Int]().withDefaultValue(0)

      private def streamOf(t: Label): Stream[Identifier] = Stream.continually(
        FreshIdentifier(t.asString, t.getType, true)
      )

      def rewind(): Unit = {
        slots = Map[Label, Int]().withDefaultValue(0)
      }

      def getNext(t: Label) = {
        if (!(buffers contains t)) {
          buffers += t -> streamOf(t)
        }

        val n = slots(t)
        slots += t -> (n+1)

        buffers(t)(n)
      }
    }

    // Candidates we have manually discarded
    var discardedCandidates = Set[Candidate]()
    // Still viable candidates (allCandidates -- discardedCandidates)
    var viableCandidates   = Set[Candidate]()

    // Update the c-tree after an increase in termsize
    def updateCTree(): Unit = {
      timers.updateCTree.start()
      def freshB() = {
        val id = FreshIdentifier("B", BooleanType, true)
        bs += id
        id
      }

      def defineCTreeFor(l: Label, c: Identifier): Unit = {
        if (!(cTree contains c)) {
          val cGen = new CGenerator()

          val alts = grammar.getProductions(l)

          val cTreeData = alts flatMap { gen =>

            // Optimize labels
            cGen.rewind()

            val subCs = for (sl <- gen.subTrees) yield {
              val subC = cGen.getNext(sl)
              defineCTreeFor(sl, subC)
              subC
            }
            
            if (subCs.forall(sc => cTree(sc).nonEmpty)) {
              val b = freshB()
              Some((b, gen.builder, subCs))
            } else None
          }

          cTree += c -> cTreeData
        }
      }

      val cGen = new CGenerator()

      rootC = {
        val c = cGen.getNext(rootLabel)
        defineCTreeFor(rootLabel, c)
        c
      }

      ifDebug { printer =>
        printer("Grammar so far:")
        grammar.printProductions(printer)
        printer("")
      }

      bsOrdered = bs.toSeq.sorted

      discardedCandidates = Set()
      viableCandidates = allCandidates().toSet

      setCExpr()

      timers.updateCTree.stop()
    }

    // Returns a count of all possible programs
    val allCandidatesCount: () => Int = {
      var nAltsCache = Map[Label, Int]()

      def countAlternatives(l: Label): Int = {
        if (!(nAltsCache contains l)) {
          val count = grammar.getProductions(l).map { gen =>
            gen.subTrees.map(countAlternatives).product
          }.sum
          nAltsCache += l -> count
        }
        nAltsCache(l)
      }

      () => countAlternatives(rootLabel)
    }

    /**
     * Returns all possible assignments to Bs in order to enumerate all possible programs
     */
    def allCandidates(): Traversable[Candidate] = {

      var cache = Map[Identifier, Seq[Candidate]]()

      val c = allCandidatesCount()

      if (c > nCandidatesLimit) {
        debug(s"Exceeded program limit: $c > $nCandidatesLimit")
        return Seq()
      }

      def allCandidatesFor(c: Identifier): Seq[Candidate] = {
        if (!(cache contains c)) {
          val subs = for ((b, _, subcs) <- cTree(c)) yield {
            if (subcs.isEmpty) {
              Seq(Set(b))
            } else {
              val subPs = subcs map (s => allCandidatesFor(s))
              val combos = SeqUtils.cartesianProduct(subPs).map(_.flatten.toSet)
              combos map (_ + b)
            }
          }
          cache += c -> subs.flatten
        }
        cache(c)
      }

      allCandidatesFor(rootC)
    }

    private def debugCTree(cTree: Map[Identifier, Seq[(Identifier, Seq[Expr] => Expr, Seq[Identifier])]],
                           markedBs: Set[Identifier] = Set()): Unit = {
      println(" -- -- -- -- -- ")
      for ((c, alts) <- cTree) {
        println()
        println(f"$c%-4s :=")
        for ((b, builder, cs) <- alts ) {
          val markS   = if (markedBs(b)) Console.GREEN else ""
          val markE   = if (markedBs(b)) Console.RESET else ""

          val ex = builder(cs.map(_.toVariable)).asString

          println(f"      $markS  ${b.asString}%-4s => $ex%-40s [${cs.map(_.asString).mkString(", ")}]$markE")
        }
      }
    }

    /**
     * Computes an expression comprised of several Let(..) and If-Then-Else
     * to represent the current cTree.
     */
    private def setCExpr(): Unit = {
      var visited = Set[Identifier]()
      val lets = new ArrayBuffer[(Identifier, Expr)]()

      def exprOf(alt: (Identifier, Seq[Expr] => Expr, Seq[Identifier])): Expr = {
        val (_, builder, cs) = alt

        builder(cs.map { c => c.toVariable })
      }

      def traverse(c: Identifier): Unit = {
        if (!visited(c)) {
          visited += c

          val alts = cTree(c)

          for ((_, _, cs) <- alts; c <- cs) {
            traverse(c)
          }

          val body = if (alts.nonEmpty) {
            alts.init.foldLeft(exprOf(alts.last)) {
              case (e, alt) => IfExpr(alt._1.toVariable, exprOf(alt), e)
            }
          } else {
            Error(c.getType, s"Empty production rule: $c")
          }

          lets += c -> body

        }
      }

      traverse(rootC)

      cExpr = simplifyLets(lets.foldRight(rootC.toVariable: Expr) {
        case ((id, rhs), body) => Let(id, rhs, body)
      })

      setSolution(cExpr)

      ifDebug { printer =>
        printer("-- "*30)
        printer(program.asString)
        printer(".. "*30)
      }
    }

    // Tests a candidate solution against an example in the correct environment
    def testCandidate(bValues: Candidate)(ex: Example): Option[Boolean] = {

      val expr = getExpr(bValues)

      def withBindings(e: Expr) = p.pc.bindings.foldRight(e) {
        case ((id, v), bd) => let(id, v, bd)
      }

      setSolution(expr)

      timers.testCandidate.start()

      val testExpr = ex match {
        case InExample(_) =>
          spec

        case InOutExample(_, outs) =>
          equality(expr, tupleWrap(outs))
      }

      val res = evaluator.eval(withBindings(testExpr), p.as.zip(ex.ins).toMap)

      timers.testCandidate.stop()

      res match {
        case EvaluationResults.Successful(res) =>
          Some(res == BooleanLiteral(true))

        case EvaluationResults.RuntimeError(err) =>
          debug("RE testing CE: "+err)
          Some(false)

        case EvaluationResults.EvaluatorError(err) =>
          debug("Error testing CE: "+err)
          None
      }

    }

    // Returns the inner expression corresponding to a B-valuation
    def getExpr(bValues: Candidate): Expr = {

      def getCValue(c: Identifier): Expr = {
        cTree(c).find(i => bValues(i._1)).map {
          case (b, builder, cs) =>
            builder(cs.map(getCValue))
        }.getOrElse {
          Error(c.getType, "Impossible assignment of bs")
        }
      }

      getCValue(rootC)
    }

    def getOuterExpr(bValues: Candidate): Expr = {
      val innerExpr = getExpr(bValues)

      innerToOuter.transform(innerExpr)(Map())
    }

    /**
     * Individually validate all candidates
     */
    def validateAllCandidates(): Option[Stream[Solution]] = {

      var untrusted: List[Solution] = Nil

      while(viableCandidates.nonEmpty) {
        val bs = viableCandidates.head

        validateCandidate(bs) match {
          case Some(sol) =>
            if (sol.isTrusted) {
              // We immediately have a good solution
              return Some(Stream(sol))
            } else {
              discardCandidate(bs, true)
              untrusted ::= sol
            }

          case None =>
            discardCandidate(bs, true)
        }
      }

      if (useOptTimeout && untrusted.nonEmpty) {
        info(s"STE could not prove the validity of the resulting ${untrusted.size} expression(s)")
        Some(untrusted.toStream)
      } else {
        None
      }
    }

    def hasViableCandidates = viableCandidates.nonEmpty

    def discardAllCandidates() = {
      discardedCandidates ++= viableCandidates
      viableCandidates = Set()
    }

    // Explicitly remove candidate computed by bValues from the search space
    //
    // If the bValues comes from models, we make sure the bValues we exclude
    // are minimal we make sure we exclude only Bs that are used.
    def discardCandidate(bs: Candidate, isMinimal: Boolean): Unit = {

      def filterBTree(c: Identifier): Set[Identifier] = {
        val (b, _, subcs) = cTree(c).find(sub => bs(sub._1)).get
        subcs.flatMap(filterBTree).toSet + b
      }

      val bvs = if (isMinimal) {
        bs
      } else {
        filterBTree(rootC)
      }

      discardedCandidates += bvs
      viableCandidates    -= bvs
    }

    def unfold() = {
      termSize_ += 1
      updateCTree()
    }

    /**
     * First phase of STE: discover potential candidates (that work on at least one input)
     * Can return one of tree values:
     *  1) Some(Some(bs)) => Found a candidate program bs
     *  2) Some(None)     => We know for sure that no candidate exists
     *  3) None           => We don't now
     */
    def discoverCandidate(): Option[Option[Candidate]] = {
      timers.tentative.start()
      val solver  = exSolverF.getNewSolver()

      try {
        setSolution(cExpr)

        val toFind = p.pc and spec

        println(toFind.asString)

        solver.assertCnstr(toFind)

        for ((c, alts) <- cTree) {

          val bs = alts.map(_._1)

          val either = for (a1 <- bs; a2 <- bs if a1 < a2) yield {
            Or(Not(a1.toVariable), Not(a2.toVariable))
          }

          if (bs.nonEmpty) {
            //println(" - "+andJoin(either).asString)
            solver.assertCnstr(andJoin(either))

            val oneOf = orJoin(bs.map(_.toVariable))
            //println(" - "+oneOf.asString)
            solver.assertCnstr(oneOf)
          }
        }

        //println(" -- Discarded:")
        for (ex <- discardedCandidates) {
          val notThisCandidate = Not(andJoin(ex.map(_.toVariable).toSeq))

          solver.assertCnstr(notThisCandidate)
        }

        solver.check match {
          case Some(true) =>
            val model = solver.getModel

            val bModel = bs.filter(b => model.get(b).contains(BooleanLiteral(true)))

            //println("Tentative model: "+model.asString)
            //println("Tentative model: "+bModel.filter(isBActive).map(_.asString).toSeq.sorted)
            //println("Tentative expr: "+getExpr(bModel))
          
            Some(Some(bModel))

          case Some(false) =>
            //println("UNSAT!")
            Some(None)

          case None =>
            /**
             * If the remaining candidates are all infeasible, it
             * might timeout instead of returning Some(false). We might still
             * benefit from unfolding further
             */
            None
        }
      } finally {
        timers.tentative.stop()
        exSolverF.reclaim(solver)
      }
    }

    /**
     * Second phase of STE: verify a given candidate by looking for CEX inputs.
     * Returns the potential solution and whether it is to be trusted.
     */
    def validateCandidate(bs: Candidate, potentialCExamples: Seq[InExample] = Nil): Option[Solution] = {
      timers.cex.start()
      val solver  = cexSolverF.getNewSolver()

      try {
        val solExpr = getExpr(bs)

        setSolution(solExpr)
        solver.assertCnstr(p.pc and not(spec))
        setSolution(solExpr)

        //println("@ "*80)
        //println("-- "*30)
        //println(program.asString)
        //println(".. "*30)
        //println("$ "*80)

        solver.check match {
          case Some(true) =>
            val model = solver.getModel
            val cex  = InExample(p.as.map(a => model.getOrElse(a, simplestValue(a.getType))))

            // Found counterexample! Exclude this program
            innerExamples += cex
            failedExamplesStats(cex) += 1

            debug(f" Program: ${getExpr(bs).asString}%-80s failed on: ${cex.asString}")

            discardCandidate(bs, false)

            // Retest whether the newly found C-E invalidates some programs
            var isBadExample = false

            for (bs2 <- viableCandidates if !isBadExample && bs2 != bs) {
              testCandidate(bs2)(cex) match {
                case Some(true) =>
                  // No-op

                case Some(false) =>
                  debug(f" Program: ${getExpr(bs2).asString}%-80s failed on: ${cex.asString}")
                  failedExamplesStats(cex) += 1
                  discardCandidate(bs2, true)

                case None =>
                  debug(s" Test $cex failed, removing...")
                  innerExamples -= cex
                  isBadExample = true
              }
            }

            None

          case Some(false) =>
            Some(Solution(BooleanLiteral(true), Set(), getOuterExpr(bs), true))

          case None =>
            if (useOptTimeout) {
              info("STE could not prove the validity of the resulting expression")
              // Interpret timeout in CE search as "the candidate is valid"
              Some(Solution(BooleanLiteral(true), Set(), getOuterExpr(bs), false))

            } else {
              discardCandidate(bs, false)

              // TODO: Make STE fail early when it times out when verifying 1 program?
              None
            }
        }
      } finally {
        timers.cex.stop()
        cexSolverF.reclaim(solver)
      }
    }

    // We keep number of failures per test to pull the better ones to the front
    val failedExamplesStats = new MutableMap[Example, Int]().withDefaultValue(0)

    val innerExamples = {
      val baseInnerExamples = outerExamples.map{ ex => ex.map(outerToInner.transform(_)(Map.empty)) }

      new GrowableIterable(baseInnerExamples, innerExamplesGenerator)
    }

    var nRequests = 1

    def getInnerExamples() = {
      if (nRequests == 10 || nRequests == 50 || nRequests % 500 == 0) {
        innerExamples.sortBufferBy(e => -failedExamplesStats(e))
      }

      nRequests += 1
      innerExamples.iterator
    }

    def nPassing = viableCandidates.size


    def filterWithExamples(): Boolean = {
      val nInitial = nPassing
      debug(s"#Candidates: $nInitial")

      debug(s"#Tests: >= ${innerExamples.bufferedCount}")

      ifDebug{ printer =>
        val es = getInnerExamples()
        for (e <- es.take(Math.min(innerExamples.bufferedCount, 10))) {
          printer(" - "+e.asString)
        }
        if(es.hasNext) {
          printer(" - ...")
        }
      }

      def filteredEnough() = {
        nPassing <= 10 || (nPassing <= 100 && nInitial / nPassing > testReductionRatio)
      }

      innerExamples.canGrow = filteredEnough

      // We further filter the set of working programs to remove those that fail on known examples
      if (innerExamples.nonEmpty) {
        timers.filter.start()
        for (bs <- viableCandidates if !interruptManager.isInterrupted) {

          var badExamples = Set[Example]()
          var stop = false

          for (e <- getInnerExamples() if !stop && !badExamples.contains(e)) {
            testCandidate(bs)(e) match {
              case Some(true) => // ok, passes
              case Some(false) =>
                // Program fails the test
                stop = true
                failedExamplesStats(e) += 1
                debug(f" Program: ${getExpr(bs).asString}%-80s failed on: ${e.asString}")
                discardCandidate(bs, true)

              case None =>
                // Eval. error -> bad example
                debug(s" Test $e crashed the evaluator, removing...")
                badExamples += e
            }
          }

          innerExamples --= badExamples
        }

        timers.filter.stop()
      }

      debug(s"#Candidates passing tests: $nPassing out of $nInitial")

      ifDebug{ printer =>
        for (p <- viableCandidates.take(100)) {
          printer(" - "+getExpr(p).asString)
        }
        if(nPassing > 100) {
          printer(" - ...")
        }
      }

      filteredEnough
    }

    updateCTree()
  }

  case class STEParams(
    grammar: ExpressionGrammar,
    rootLabel: TypeTree => Label,
    optimizations: Boolean,
    sizes: List[(Int, Int, Int)]
  )

  def getParams(sctx: SynthesisContext, p: Problem): STEParams

  def instantiateOn(implicit hctx: SearchContext, p: Problem): Traversable[RuleInstantiation] = {

    import hctx.reporter._

    val interruptManager = hctx.interruptManager

    // Timeout to solve the pc for at least one valid input
    val pcSolverTo = 1000L

    if (p.isTestBased) {
      return Nil
    }


    val sizes = getParams(hctx, p).sizes

    sizes.collect { case (sizeFrom, sizeTo, cost) if sizeFrom <= sizeTo =>
      val solBuilder = SolutionBuilderCloser(extraCost = Cost(cost))

      new RuleInstantiation(s"${this.name} ($sizeFrom->$sizeTo)", solBuilder) {
        def apply(hctx: SearchContext): RuleApplication = {
          var result: Option[RuleApplication] = None

          val timers = hctx.timers.synthesis.applications.STE

          implicit val ic = hctx

          debug("Acquiring initial list of examples")

          // To the list of known examples, we add an additional one produced by the solver
          val solverExample = if (p.pc.isEmpty) {
            List(InExample(p.as.map(a => simplestValue(a.getType))))
          } else {
            val solverf = hctx.solverFactory
            val solver  = solverf.getNewSolver().setTimeout(pcSolverTo)

            solver.assertCnstr(p.pc.toClause)

            try {
              solver.check match {
                case Some(true) =>
                  val model = solver.getModel
                  List(InExample(p.as.map(a => model.getOrElse(a, simplestValue(a.getType)))))

                case Some(false) =>
                  debug("Path-condition seems UNSAT")
                  return RuleFailed()

                case None =>
                  if (!interruptManager.isInterrupted) {
                    warning("Solver could not solve path-condition")
                  }
                  return RuleFailed() // This is not necessary though, but probably wanted
              }
            } finally {
              solverf.reclaim(solver)
            }
          }

          val baseExampleInputs = p.qebFiltered.examples ++ solverExample

          ifDebug { debug =>
            baseExampleInputs.foreach { in =>
              debug("  - "+in.asString)
            }
          }


          // Represents a non-deterministic program
          val ndProgram = new NonDeterministicProgram(
            interruptManager = interruptManager,
            outerCtx = hctx,
            outerP   = p,
            initSize = sizeFrom - 1,
            outerExamples = baseExampleInputs
          )

          try {
            do {
              // Run STE for one specific unfolding level
              ndProgram.unfold()

              val filteredEnough = ndProgram.filterWithExamples()

                // STE Loop at a given unfolding level
              while (result.isEmpty && !interruptManager.isInterrupted && ndProgram.hasViableCandidates) {
                debug("Candidates left: " + ndProgram.viableCandidates.size)

                // Phase 0: If the number of remaining programs is small, validate them individually
                if (filteredEnough) {
                  timers.validate.start()

                  debug(s"Will send ${ndProgram.nPassing} program(s) to validate individually")

                  ndProgram.validateAllCandidates() match {
                    case Some(sols) =>
                      // Found solution! Exit STE
                      result = Some(RuleClosed(sols))

                    case None =>
                      debug(s"#Candidates after validating individually: ${ndProgram.nPassing}")
                  }

                  timers.validate.stop()
                }

                if (result.isEmpty && ndProgram.hasViableCandidates) {
                  // Phase 1: Find a candidate program that works for at least 1 input
                  debug("Looking for program that works on at least 1 input...")

                  ndProgram.discoverCandidate() match {
                    case Some(Some(bs)) =>
                      debug(s"Found candidate: ${ndProgram.getExpr(bs)}")

                      // Phase 2: Validate candidate model
                      ndProgram.validateCandidate(bs) match {
                        case Some(sol) =>
                          result = Some(RuleClosed(sol))

                        case None =>

                      }

                    case Some(None) =>
                      debug("There exists no candidate program!")
                      ndProgram.discardAllCandidates()

                    case None =>
                      debug("Timeout while getting tentative program!")
                      ndProgram.discardAllCandidates()
                      // TODO: Make STE fail early when it times out when looking for tentative program?
                      //result = Some(RuleFailed())
                  }
                }
              }
            } while(ndProgram.termSize < sizeTo && result.isEmpty && !interruptManager.isInterrupted)

            if (interruptManager.isInterrupted) {
              interruptManager.recoverInterrupt()
            }

            result.getOrElse(RuleFailed())
          } catch {
            case e: Throwable =>
              warning("STE crashed: "+e.getMessage)
              e.printStackTrace()
              RuleFailed()
          }
        }
      }
    }
  }
}
