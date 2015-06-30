/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package synthesis
package rules

import leon.utils.SeqUtils
import solvers._
import solvers.z3._

import purescala.Expressions._
import purescala.Common._
import purescala.Definitions._
import purescala.Types._
import purescala.ExprOps._
import purescala.DefOps._
import purescala.Constructors._

import scala.collection.mutable.{HashMap=>MutableMap, ArrayBuffer}

import evaluators._
import datagen._
import codegen.CodeGenParams

import utils._
import utils.ExpressionGrammars.{SizeBoundedGrammar, SizedLabel}
import bonsai.Generator

abstract class CEGISLike[T <% Typed](name: String) extends Rule(name) {

  case class CegisParams(
    grammar: ExpressionGrammar[T],
    rootLabel: TypeTree => T,
    maxUnfoldings: Int = 5
  )

  def getParams(sctx: SynthesisContext, p: Problem): CegisParams

  def instantiateOn(implicit hctx: SearchContext, p: Problem): Traversable[RuleInstantiation] = {
    val exSolverTo  = 2000L
    val cexSolverTo = 2000L

    // Track non-deterministic programs up to 50'000 programs, or give up
    val nProgramsLimit = 100000

    val sctx = hctx.sctx
    implicit val ctx  = sctx.context


    // CEGIS Flags to activate or deactivate features
    val useOptTimeout         = sctx.settings.cegisUseOptTimeout.getOrElse(true)
    val useVanuatoo           = sctx.settings.cegisUseVanuatoo.getOrElse(false)
    val useShrink             = sctx.settings.cegisUseShrink.getOrElse(true)

    // Limits the number of programs CEGIS will specifically validate individually
    val validateUpTo          = 5

    // Shrink the program when the ratio of passing cases is less than the threshold
    val shrinkThreshold       = 1.0/2

    val interruptManager      = sctx.context.interruptManager

    val params = getParams(sctx, p)

    if (params.maxUnfoldings == 0) {
      return Nil
    }

    class NonDeterministicProgram(val p: Problem, initTermSize: Int = 1) {

      private var termSize = 0;

      val grammar = ExpressionGrammars.SizeBoundedGrammar(params.grammar)

      def rootLabel(tpe: TypeTree) = SizedLabel(params.rootLabel(tpe), termSize)

      def xLabels = p.xs.map(x => rootLabel(x.getType))

      var nAltsCache = Map[SizedLabel[T], Int]()

      def countAlternatives(l: SizedLabel[T]): Int = {
        if (!(nAltsCache contains l)) {
          val count = grammar.getProductions(l).map {
            case Generator(subTrees, _) => subTrees.map(countAlternatives).product
          }.sum
          nAltsCache += l -> count
        }
        nAltsCache(l)
      }

      def allProgramsCount(): Int = {
        xLabels.map(countAlternatives).product
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
       *         (b1, F(c2, c3), Set(c2, c3))
       *         (b2, G(c4, c5), Set(c4, c5))
       *       )
       * c6 -> Seq(
       *         (b3, H(c7, c8), Set(c7, c8))
       *       )
       */
      private var cTree: Map[Identifier, Seq[(Identifier, Seq[Expr] => Expr, Seq[Identifier])]] = Map()


      // C identifiers corresponding to p.xs
      private var rootCs: Seq[Identifier]    = Seq()

      private var bs: Set[Identifier]        = Set()

      private var bsOrdered: Seq[Identifier] = Seq()




      class CGenerator {
        private var buffers = Map[SizedLabel[T], Stream[Identifier]]()

        private var slots = Map[SizedLabel[T], Int]().withDefaultValue(0)

        private def streamOf(t: SizedLabel[T]): Stream[Identifier] = {
          FreshIdentifier(t.toString, t.getType, true) #:: streamOf(t)
        }

        def rewind(): Unit = {
          slots = Map[SizedLabel[T], Int]().withDefaultValue(0)
        }

        def getNext(t: SizedLabel[T]) = {
          if (!(buffers contains t)) {
            buffers += t -> streamOf(t)
          }

          val n = slots(t)
          slots += t -> (n+1)

          buffers(t)(n)
        }
      }

      def init(): Unit = {
        updateCTree()
      }


      def updateCTree(): Unit = {
        def freshB() = {
          val id = FreshIdentifier("B", BooleanType, true)
          bs += id
          id
        }

        def defineCTreeFor(l: SizedLabel[T], c: Identifier): Unit = {
          if (!(cTree contains c)) {
            val cGen = new CGenerator()

            var alts = grammar.getProductions(l)

            val cTreeData = for (gen <- alts) yield {
              val b = freshB()

              // Optimize labels
              cGen.rewind()

              val subCs = for (sl <- gen.subTrees) yield {
                val subC = cGen.getNext(sl)
                defineCTreeFor(sl, subC)
                subC
              }

              (b, gen.builder, subCs)
            }

            cTree += c -> cTreeData
          }
        }

        val cGen = new CGenerator()

        rootCs = for (l <- xLabels) yield {
          val c = cGen.getNext(l)
          defineCTreeFor(l, c)
          c
        }

        sctx.reporter.ifDebug { printer =>
          printer("Grammar so far:")
          grammar.printProductions(printer)
        }

        bsOrdered    = bs.toSeq.sortBy(_.id)

        setCExpr(computeCExpr())
      }

      /**
       * Keeps track of blocked Bs and which C are affected, assuming cs are undefined:
       *
       * b2 -> Set(c4)
       * b3 -> Set(c4)
       */
      private var closedBs: Map[Identifier, Set[Identifier]] = Map()

      /**
       * Checks if 'b' is closed (meaning it depends on uninterpreted terms)
       */
      def isBActive(b: Identifier) = !closedBs.contains(b)


      /**
       * Returns all possible assignments to Bs in order to enumerate all possible programs
       */
      def allPrograms(): Traversable[Set[Identifier]] = {

        val allCount = allProgramsCount()
        if (allCount > nProgramsLimit) {
          ctx.reporter.debug(s"Exceeded program limit: $allCount > $nProgramsLimit")
          return Seq()
        }

        var cache = Map[Identifier, Seq[Set[Identifier]]]()

        def allProgramsFor(cs: Seq[Identifier]): Seq[Set[Identifier]] = {
          val seqs = for (c <- cs.toSeq) yield {
            if (!(cache contains c)) {
              val subs = for ((b, _, subcs) <- cTree(c) if isBActive(b)) yield {
                if (subcs.isEmpty) {
                  Seq(Set(b))
                } else {
                  for (p <- allProgramsFor(subcs)) yield {
                    p + b
                  }
                }
              }
              cache += c -> subs.flatten
            }
            cache(c)
          }

          SeqUtils.cartesianProduct(seqs).map { ls =>
            ls.foldLeft(Set[Identifier]())(_ ++ _)
          }
        }

        allProgramsFor(rootCs)
      }

      private def debugCTree(cTree: Map[Identifier, Seq[(Identifier, Seq[Expr] => Expr, Seq[Identifier])]],
                             markedBs: Set[Identifier] = Set()): Unit = {
        println(" -- -- -- -- -- ")
        for ((c, alts) <- cTree) {
          println
          println(f"$c%-4s :=")
          for ((b, builder, cs) <- alts ) {
            val active = if (isBActive(b)) " " else "⨯"
            val markS   = if (markedBs(b)) Console.GREEN else ""
            val markE   = if (markedBs(b)) Console.RESET else ""

            val ex = builder(cs.map(_.toVariable)).asString

            println(f"      $markS$active  ${b.asString}%-4s => $ex%-40s [${cs.map(_.asString).mkString(", ")}]$markE")
          }
        }
      }

      private def computeCExpr(): (Expr, Seq[FunDef]) = {
        var cToFd = Map[Identifier, FunDef]()

        def exprOf(alt: (Identifier, Seq[Expr] => Expr, Seq[Identifier])): Expr = {
          val (_, builder, cs) = alt

          val e = builder(cs.map { c =>
            val fd = cToFd(c)
            FunctionInvocation(fd.typed, fd.params.map(_.toVariable))
          })

          outerExprToInnerExpr(e)
        }

        // Define all C-def
        for ((c, alts) <- cTree) yield {
          cToFd += c -> new FunDef(FreshIdentifier(c.toString, alwaysShowUniqueID = true),
                                   Seq(),
                                   c.getType,
                                   p.as.map(id => ValDef(id)))
        }

        // Fill C-def bodies
        for ((c, alts) <- cTree) {
          val activeAlts = alts.filter(a => isBActive(a._1))

          val body = if (activeAlts.nonEmpty) {
            activeAlts.init.foldLeft(exprOf(activeAlts.last)) {
              case (e, alt) => IfExpr(alt._1.toVariable, exprOf(alt), e)
            }
          } else {
            Error(c.getType, "Impossibru")
          }

          cToFd(c).fullBody = body
        }

        // Top-level expression for rootCs
        val expr = tupleWrap(rootCs.map { c =>
          val fd = cToFd(c)
          FunctionInvocation(fd.typed, fd.params.map(_.toVariable))
        })

        (expr, cToFd.values.toSeq)
      }



      private val cTreeFd = new FunDef(FreshIdentifier("cTree", alwaysShowUniqueID = true),
                               Seq(),
                               p.outType,
                               p.as.map(id => ValDef(id))
                             )

      private val phiFd   = new FunDef(FreshIdentifier("phiFd", alwaysShowUniqueID = true),
                               Seq(),
                               BooleanType,
                               p.as.map(id => ValDef(id))
                             )


      private val (innerProgram, origFdMap) = {

        val outerSolution = {
          new PartialSolution(hctx.search.g, true)
            .solutionAround(hctx.currentNode)(FunctionInvocation(cTreeFd.typed, p.as.map(_.toVariable)))
            .getOrElse(ctx.reporter.fatalError("Unable to get outer solution"))
        }

        val program0 = addFunDefs(sctx.program, Seq(cTreeFd, phiFd) ++ outerSolution.defs, hctx.ci.fd)

        cTreeFd.body = None
        phiFd.body   = Some(
          letTuple(p.xs,
                   FunctionInvocation(cTreeFd.typed, p.as.map(_.toVariable)),
                   p.phi)
        )

        replaceFunDefs(program0){
          case fd if fd == hctx.ci.fd =>
            val nfd = fd.duplicate

            nfd.fullBody = postMap {
              case src if src eq hctx.ci.source =>
                Some(outerSolution.term)

              case _ => None
            }(nfd.fullBody)

            Some(nfd)

          // We freshen/duplicate every functions, except these two as they are
          // fresh anyway and we refer to them directly.
          case `cTreeFd` | `phiFd` =>
            None

          case fd =>
            Some(fd.duplicate)
        }

      }

      /**
       * Since CEGIS works with a copy of the program, it needs to map outer
       * function calls to inner function calls and vice-versa. 'inner' refers
       * to the CEGIS-specific program, 'outer' refers to the actual program on
       * which we do synthesis.
       */
      private def outerExprToInnerExpr(e: Expr): Expr = {
        replaceFunCalls(e, {fd => origFdMap.getOrElse(fd, fd) })
      }

      private val innerPc  = outerExprToInnerExpr(p.pc)
      private val innerPhi = outerExprToInnerExpr(p.phi)

      private var programCTree: Program = _
      private var tester: (Seq[Expr], Set[Identifier]) => EvaluationResults.Result = _

      private def setCExpr(cTreeInfo: (Expr, Seq[FunDef])): Unit = {
        val (cTree, newFds) = cTreeInfo

        cTreeFd.body = Some(cTree)
        programCTree = addFunDefs(innerProgram, newFds, cTreeFd)

        //println("-- "*30)
        //println(programCTree.asString)
        //println(".. "*30)

//        val evaluator  = new DualEvaluator(sctx.context, programCTree, CodeGenParams.default)
        val evaluator  = new DefaultEvaluator(sctx.context, programCTree)

        tester =
          { (ins: Seq[Expr], bValues: Set[Identifier]) =>
            val envMap = bs.map(b => b -> BooleanLiteral(bValues(b))).toMap

            val fi = FunctionInvocation(phiFd.typed, ins)

            evaluator.eval(fi, envMap)
          }
      }


      def testForProgram(bValues: Set[Identifier])(ins: Seq[Expr]): Boolean = {
        tester(ins, bValues) match {
          case EvaluationResults.Successful(res) =>
            res == BooleanLiteral(true)

          case EvaluationResults.RuntimeError(err) =>
            sctx.reporter.warning("RE testing CE: "+err)
            false

          case EvaluationResults.EvaluatorError(err) =>
            sctx.reporter.error("Error testing CE: "+err)
            false
        }
      }



      // Returns the outer expression corresponding to a B-valuation
      def getExpr(bValues: Set[Identifier]): Expr = {
        def getCValue(c: Identifier): Expr = {
          cTree(c).find(i => bValues(i._1)).map {
            case (b, builder, cs) =>
              builder(cs.map(getCValue))
          }.getOrElse {
            simplestValue(c.getType)
          }
        }

        tupleWrap(rootCs.map(c => getCValue(c)))
      }

      /**
       * Here we check the validity of a given program in isolation, we compute
       * the corresponding expr and replace it in place of the C-tree
       */
      def validatePrograms(bss: Set[Set[Identifier]]): Either[Stream[Solution], Seq[Seq[Expr]]] = {
        val origImpl = cTreeFd.fullBody

        val cexs = for (bs <- bss.toSeq) yield {
          val outerSol = getExpr(bs)
          val innerSol = outerExprToInnerExpr(outerSol)

          cTreeFd.fullBody = innerSol

          val cnstr = and(innerPc, letTuple(p.xs, innerSol, Not(innerPhi)))

          //println("Solving for: "+cnstr.asString)

          val solverf = SolverFactory.default(ctx, innerProgram).withTimeout(cexSolverTo)
          val solver  = solverf.getNewSolver()
          try {
            solver.assertCnstr(cnstr)
            solver.check match {
              case Some(true) =>
                excludeProgram(bs)
                val model = solver.getModel
                //println("Found counter example: ")
                //for ((s, v) <- model) {
                //  println(" "+s.asString+" -> "+v.asString)
                //}

                //val evaluator  = new DefaultEvaluator(ctx, prog)
                //println(evaluator.eval(cnstr, model))

                Some(p.as.map(a => model.getOrElse(a, simplestValue(a.getType))))

              case Some(false) =>
                // UNSAT, valid program
                return Left(Stream(Solution(BooleanLiteral(true), Set(), outerSol, true)))

              case None =>
                if (useOptTimeout) {
                  // Interpret timeout in CE search as "the candidate is valid"
                  sctx.reporter.info("CEGIS could not prove the validity of the resulting expression")
                  // Optimistic valid solution
                  return Left(Stream(Solution(BooleanLiteral(true), Set(), outerSol, false)))
                } else {
                  None
                }
            }
          } finally {
            solver.free()
            solverf.shutdown()
            cTreeFd.fullBody = origImpl
          }
        }

        Right(cexs.flatten)
      }

      var excludedPrograms = ArrayBuffer[Set[Identifier]]()

      // Explicitly remove program computed by bValues from the search space
      def excludeProgram(bValues: Set[Identifier]): Unit = {
        val bvs = bValues.filter(isBActive)
        excludedPrograms += bvs
      }

      def unfold(finalUnfolding: Boolean): Boolean = {
        termSize += 1
        updateCTree()
        true
      }

      /**
       * First phase of CEGIS: solve for potential programs (that work on at least one input)
       */
      def solveForTentativeProgram(): Option[Option[Set[Identifier]]] = {
        val solverf = SolverFactory.default(ctx, programCTree).withTimeout(exSolverTo)
        val solver  = solverf.getNewSolver()
        val cnstr = FunctionInvocation(phiFd.typed, phiFd.params.map(_.id.toVariable))
        //debugCExpr(cTree)

        //println(" --- PhiFD ---")
        //println(phiFd.fullBody.asString(ctx))

        val fixedBs = finiteArray(bsOrdered.map(_.toVariable), None, BooleanType)

        val toFind = and(innerPc, cnstr)
        //println(" --- Constraints ---")
        //println(" - "+toFind)
        try {
          solver.assertCnstr(andJoin(bsOrdered.map(b => if (bs(b)) b.toVariable else Not(b.toVariable))))
          solver.assertCnstr(toFind)

          for ((c, alts) <- cTree) {
            val activeBs = alts.map(_._1).filter(isBActive)

            val either = for (a1 <- activeBs; a2 <- activeBs if a1.globalId < a2.globalId) yield {
              Or(Not(a1.toVariable), Not(a2.toVariable))
            }

            if (activeBs.nonEmpty) {
              //println(" - "+andJoin(either))
              solver.assertCnstr(andJoin(either))

              val oneOf = orJoin(activeBs.map(_.toVariable))
              //println(" - "+oneOf)
              solver.assertCnstr(oneOf)
            }
          }

          //println(" -- Excluded:")
          //println(" -- Active:")
          val isActive = andJoin(bsOrdered.filterNot(isBActive).map(id => Not(id.toVariable)))
          //println("  - "+isActive)
          solver.assertCnstr(isActive)

          //println(" -- Excluded:")
          for (ex <- excludedPrograms) {
            val notThisProgram = Not(andJoin(ex.map(_.toVariable).toSeq))

            //println(f"  - $notThisProgram%-40s ("+getExpr(ex)+")")
            solver.assertCnstr(notThisProgram)
          }

          solver.check match {
            case Some(true) =>
              val model = solver.getModel

              val bModel = bs.filter(b => model.get(b).contains(BooleanLiteral(true)))

              //println("Tentative expr: "+getExpr(bModel))
              Some(Some(bModel))

            case Some(false) =>
              //println("UNSAT!")
              Some(None)

            case None =>
              /**
               * If the remaining tentative programs are all infeasible, it
               * might timeout instead of returning Some(false). We might still
               * benefit from unfolding further
               */
              ctx.reporter.debug("Timeout while getting tentative program!")
              Some(None)
          }
        } finally {
          solver.free()
          solverf.shutdown()
        }
      }

      /**
       * Second phase of CEGIS: verify a given program by looking for CEX inputs
       */
      def solveForCounterExample(bs: Set[Identifier]): Option[Option[Seq[Expr]]] = {
        val solverf = SolverFactory.default(ctx, programCTree).withTimeout(cexSolverTo)
        val solver  = solverf.getNewSolver()
        val cnstr = FunctionInvocation(phiFd.typed, phiFd.params.map(_.id.toVariable))


        try {
          solver.assertCnstr(andJoin(bsOrdered.map(b => if (bs(b)) b.toVariable else Not(b.toVariable))))
          solver.assertCnstr(innerPc)
          solver.assertCnstr(Not(cnstr))

          solver.check match {
            case Some(true) =>
              val model = solver.getModel
              val cex = p.as.map(a => model.getOrElse(a, simplestValue(a.getType)))

              Some(Some(cex))

            case Some(false) =>
              Some(None)

            case None =>
              None
          }
        } finally {
          solver.free()
          solverf.shutdown()
        }
      }

      def free(): Unit = {

      }
    }

    List(new RuleInstantiation(this.name) {
      def apply(hctx: SearchContext): RuleApplication = {
        var result: Option[RuleApplication]   = None
        val sctx = hctx.sctx

        val ndProgram = new NonDeterministicProgram(p)
        ndProgram.init()

        var unfolding = 1
        val maxUnfoldings = params.maxUnfoldings

        sctx.reporter.debug(s"maxUnfoldings=$maxUnfoldings")

        var baseExampleInputs: ArrayBuffer[Seq[Expr]] = new ArrayBuffer[Seq[Expr]]()

        sctx.reporter.ifDebug { printer =>
          ndProgram.grammar.printProductions(printer)
        }

        // We populate the list of examples with a predefined one
        sctx.reporter.debug("Acquiring initial list of examples")

        baseExampleInputs ++= p.tb.examples.map(_.ins).toSet

        if (p.pc == BooleanLiteral(true)) {
          baseExampleInputs += p.as.map(a => simplestValue(a.getType))
        } else {
          val solver = sctx.newSolver.setTimeout(exSolverTo)

          solver.assertCnstr(p.pc)

          try {
            solver.check match {
              case Some(true) =>
                val model = solver.getModel
                baseExampleInputs += p.as.map(a => model.getOrElse(a, simplestValue(a.getType)))

              case Some(false) =>
                sctx.reporter.debug("Path-condition seems UNSAT")
                return RuleFailed()

              case None =>
                sctx.reporter.warning("Solver could not solve path-condition")
                return RuleFailed() // This is not necessary though, but probably wanted
            }
          } finally {
            solver.free()
          }
        }

        sctx.reporter.ifDebug { debug =>
          baseExampleInputs.foreach { in =>
            debug("  - "+in.map(_.asString).mkString(", "))
          }
        }


        /**
         * We generate tests for discarding potential programs
         */
        val inputIterator: Iterator[Seq[Expr]] = if (useVanuatoo) {
          new VanuatooDataGen(sctx.context, sctx.program).generateFor(p.as, p.pc, 20, 3000)
        } else {
          val evaluator  = new DualEvaluator(sctx.context, sctx.program, CodeGenParams.default)
          new GrammarDataGen(evaluator, ExpressionGrammars.ValueGrammar).generateFor(p.as, p.pc, 20, 1000)
        }

        val cachedInputIterator = new Iterator[Seq[Expr]] {
          def next() = {
            val i = inputIterator.next()
            baseExampleInputs += i
            i
          }

          def hasNext = {
            inputIterator.hasNext
          }
        }

        val failedTestsStats = new MutableMap[Seq[Expr], Int]().withDefaultValue(0)

        def hasInputExamples = baseExampleInputs.size > 0 || cachedInputIterator.hasNext

        var n = 1
        def allInputExamples() = {
          if (n % 1000 == 0) {
            baseExampleInputs = baseExampleInputs.sortBy(e => -failedTestsStats(e))
          }
          n += 1
          baseExampleInputs.iterator ++ cachedInputIterator
        }

        try {
          do {
            var skipCESearch = false

            // Unfold formula
            val unfoldSuccess = ndProgram.unfold(unfolding == maxUnfoldings)

            if (!unfoldSuccess) {
              unfolding = maxUnfoldings
            }

            // Compute all programs that have not been excluded yet
            var prunedPrograms: Set[Set[Identifier]] = ndProgram.allPrograms().toSet

            val nInitial = prunedPrograms.size
            sctx.reporter.debug("#Programs: "+nInitial)
            //sctx.reporter.ifDebug{ printer =>
            //  val limit = 100

            //  for (p <- prunedPrograms.take(limit)) {
            //    val ps = p.toSeq.sortBy(_.id).mkString(", ")
            //    printer(f" - $ps%-40s - "+ndProgram.getExpr(p))
            //  }
            //  if(nInitial > limit) {
            //    printer(" - ...")
            //  }
            //}

            var wrongPrograms = Set[Set[Identifier]]()

            // We further filter the set of working programs to remove those that fail on known examples
            if (hasInputExamples) {
              for (bs <- prunedPrograms if !interruptManager.isInterrupted) {
                var valid = true
                val examples = allInputExamples()
                while(valid && examples.hasNext) {
                  val e = examples.next()
                  if (!ndProgram.testForProgram(bs)(e)) {
                    failedTestsStats(e) += 1
                    sctx.reporter.debug(f" Program: ${ndProgram.getExpr(bs).asString}%-80s failed on: ${e.map(_.asString).mkString(", ")}")
                    wrongPrograms += bs
                    prunedPrograms -= bs

                    valid = false
                  }
                }

                if (wrongPrograms.size+1 % 1000 == 0) {
                  sctx.reporter.debug("..."+wrongPrograms.size)
                }
              }
            }

            val nPassing = prunedPrograms.size
            sctx.reporter.debug("#Programs passing tests: "+nPassing)
            sctx.reporter.ifDebug{ printer =>
              for (p <- prunedPrograms.take(10)) {
                printer(" - "+ndProgram.getExpr(p))
              }
              if(nPassing > 10) {
                printer(" - ...")
              }
            }
            sctx.reporter.debug("#Tests: "+baseExampleInputs.size)
            sctx.reporter.ifDebug{ printer =>
              for (i <- baseExampleInputs.take(10)) {
                printer(" - "+i.mkString(", "))
              }
              if(baseExampleInputs.size > 10) {
                printer(" - ...")
              }
            }


            if (nPassing == 0 || interruptManager.isInterrupted) {
              // No test passed, we can skip solver and unfold again, if possible
              skipCESearch = true
            } else {
              var doFilter = true

              if (validateUpTo > 0) {
                // Validate the first N programs individualy
                ndProgram.validatePrograms(prunedPrograms.take(validateUpTo)) match {
                  case Left(sols) if sols.nonEmpty =>
                    doFilter = false
                    result = Some(RuleClosed(sols))
                  case Right(cexs) =>
                    baseExampleInputs ++= cexs

                    if (nPassing <= validateUpTo) {
                      // All programs failed verification, we filter everything out and unfold
                      //ndProgram.shrinkTo(Set(), unfolding == maxUnfoldings)
                      doFilter     = false
                      skipCESearch = true
                    }
                }
              }

              if (doFilter) {
                if (nPassing < nInitial * shrinkThreshold && useShrink) {
                  // We shrink the program to only use the bs mentionned
                  val bssToKeep = prunedPrograms.foldLeft(Set[Identifier]())(_ ++ _)
                  //ndProgram.shrinkTo(bssToKeep, unfolding == maxUnfoldings)
                } else {
                  wrongPrograms.foreach {
                    ndProgram.excludeProgram
                  }
                }
              }
            }

            // CEGIS Loop at a given unfolding level
            while (result.isEmpty && !skipCESearch && !interruptManager.isInterrupted) {

              ndProgram.solveForTentativeProgram() match {
                case Some(Some(bs)) =>
                  // Should we validate this program with Z3?

                  val validateWithZ3 = if (hasInputExamples) {

                    if (allInputExamples().forall(ndProgram.testForProgram(bs))) {
                      // All valid inputs also work with this, we need to
                      // make sure by validating this candidate with z3
                      true
                    } else {
                      // One valid input failed with this candidate, we can skip
                      ndProgram.excludeProgram(bs)
                      false
                    }
                  } else {
                    // No inputs or capability to test, we need to ask Z3
                    true
                  }

                  if (validateWithZ3) {
                    ndProgram.solveForCounterExample(bs) match {
                      case Some(Some(inputsCE)) =>
                        // Found counter example!
                        baseExampleInputs += inputsCE

                        // Retest whether the newly found C-E invalidates all programs
                        if (prunedPrograms.forall(p => !ndProgram.testForProgram(p)(inputsCE))) {
                          skipCESearch = true
                        } else {
                          ndProgram.excludeProgram(bs)
                        }

                      case Some(None) =>
                        // Found no counter example! Program is a valid solution
                        val expr = ndProgram.getExpr(bs)
                        result = Some(RuleClosed(Solution(BooleanLiteral(true), Set(), expr)))

                      case None =>
                        // We are not sure
                        if (useOptTimeout) {
                          // Interpret timeout in CE search as "the candidate is valid"
                          sctx.reporter.info("CEGIS could not prove the validity of the resulting expression")
                          val expr = ndProgram.getExpr(bs)
                          result = Some(RuleClosed(Solution(BooleanLiteral(true), Set(), expr, isTrusted = false)))
                        } else {
                          result = Some(RuleFailed())
                        }
                      }
                    }

                case Some(None) =>
                  skipCESearch = true

                case None =>
                  result = Some(RuleFailed())
              }
            }

            unfolding += 1
          } while(unfolding <= maxUnfoldings && result.isEmpty && !interruptManager.isInterrupted)

          result.getOrElse(RuleFailed())

        } catch {
          case e: Throwable =>
            sctx.reporter.warning("CEGIS crashed: "+e.getMessage)
            e.printStackTrace()
            RuleFailed()
        } finally {
          ndProgram.free()
        }
      }
    })
  }
}
