/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package synthesis
package rules

import purescala.Expressions._
import purescala.Common._
import purescala.Definitions._
import purescala.Types._
import purescala.ExprOps._
import purescala.DefOps._
import purescala.Constructors._

import solvers._
import grammars._
import grammars.transformers._
import leon.utils._

import evaluators._
import datagen._
import codegen.CodeGenParams

import scala.collection.mutable.{HashMap => MutableMap}

abstract class CEGISLike[T <: Typed](name: String) extends Rule(name) {

  case class CegisParams(
    grammar: ExpressionGrammar[T],
    rootLabel: TypeTree => T,
    optimizations: Boolean,
    maxSize: Option[Int] = None
  )

  def getParams(sctx: SynthesisContext, p: Problem): CegisParams

  def instantiateOn(implicit hctx: SearchContext, p: Problem): Traversable[RuleInstantiation] = {

    val exSolverTo  = 2000L
    val cexSolverTo = 2000L

    // Track non-deterministic programs up to 100'000 programs, or give up
    val nProgramsLimit = 100000

    val sctx = hctx.sctx
    val ctx  = sctx.context

    val timers = ctx.timers.synthesis.cegis

    // CEGIS Flags to activate or deactivate features
    val useOptTimeout = sctx.settings.cegisUseOptTimeout
    val useVanuatoo   = sctx.settings.cegisUseVanuatoo

    // The factor by which programs need to be reduced by testing before we validate them individually
    val testReductionRatio = 10

    val interruptManager = sctx.context.interruptManager

    val params = getParams(sctx, p)

    // If this CEGISLike forces a maxSize, take it, otherwise find it in the settings
    val maxSize = params.maxSize.getOrElse(sctx.settings.cegisMaxSize)

    if (maxSize == 0) {
      return Nil
    }

    // Represents a non-deterministic program
    object NonDeterministicProgram {

      // Current synthesized term size
      private var termSize = 0

      def unfolding = termSize

      val grammar = SizeBoundedGrammar(params.grammar, params.optimizations)

      def rootLabel = SizedNonTerm(params.rootLabel(tupleTypeWrap(p.xs.map(_.getType))), termSize)

      def init(): Unit = {
        updateCTree()
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

      // Top-level C identifiers corresponding to p.xs
      private var rootC: Identifier          = _

      // Blockers
      private var bs: Set[Identifier]        = Set()

      private var bsOrdered: Seq[Identifier] = Seq()

      // Generator of fresh cs that minimizes labels
      class CGenerator {
        private var buffers = Map[SizedNonTerm[T], Stream[Identifier]]()

        private var slots = Map[SizedNonTerm[T], Int]().withDefaultValue(0)

        private def streamOf(t: SizedNonTerm[T]): Stream[Identifier] = Stream.continually(
          FreshIdentifier(t.asString, t.getType, true)
        )

        def rewind(): Unit = {
          slots = Map[SizedNonTerm[T], Int]().withDefaultValue(0)
        }

        def getNext(t: SizedNonTerm[T]) = {
          if (!(buffers contains t)) {
            buffers += t -> streamOf(t)
          }

          val n = slots(t)
          slots += t -> (n+1)

          buffers(t)(n)
        }
      }

      // Programs we have manually excluded
      var excludedPrograms = Set[Set[Identifier]]()
      // Still live programs (allPrograms -- excludedPrograms)
      var prunedPrograms   = Set[Set[Identifier]]()

      // Update the c-tree after an increase in termsize
      def updateCTree(): Unit = {
        ctx.timers.synthesis.cegis.updateCTree.start()
        def freshB() = {
          val id = FreshIdentifier("B", BooleanType, true)
          bs += id
          id
        }

        def defineCTreeFor(l: SizedNonTerm[T], c: Identifier): Unit = {
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

        sctx.reporter.ifDebug { printer =>
          printer("Grammar so far:")
          grammar.printProductions(printer)
          printer("")
        }

        bsOrdered = bs.toSeq.sorted
        setCExpr()

        excludedPrograms = Set()
        prunedPrograms = allPrograms().toSet

        ctx.timers.synthesis.cegis.updateCTree.stop()
      }

      // Returns a count of all possible programs
      val allProgramsCount: () => Int = {

        var nAltsCache = Map[SizedNonTerm[T], Int]()

        def countAlternatives(l: SizedNonTerm[T]): Int = {
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
      def allPrograms(): Traversable[Set[Identifier]] = {

        val allCount = allProgramsCount()
        if (allCount > nProgramsLimit) {
          ctx.reporter.debug(s"Exceeded program limit: $allCount > $nProgramsLimit")
          return Seq()
        }

        var cache = Map[Identifier, Seq[Set[Identifier]]]()

        def allProgramsFor(cs: Seq[Identifier]): Seq[Set[Identifier]] = {
          val seqs = for (c <- cs) yield {
            if (!(cache contains c)) {
              val subs = for ((b, _, subcs) <- cTree(c)) yield {
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

          SeqUtils.cartesianProduct(seqs).map(_.flatten.toSet)
        }

        allProgramsFor(Seq(rootC))
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

      // The function which calls the synthesized expression within programCTree
      private val cTreeFd = new FunDef(FreshIdentifier("cTree", alwaysShowUniqueID = true), Seq(), p.as.map(id => ValDef(id)), p.outType)

      // Same as cTreeFd, but ensuring the spec of the problem
      private val solFd = new FunDef(FreshIdentifier("solFd", alwaysShowUniqueID = true), Seq(), p.as.map(id => ValDef(id)), p.outType)

      // The spec of the problem
      private val phiFd = new FunDef(FreshIdentifier("phiFd", alwaysShowUniqueID = true), Seq(), p.as.map(id => ValDef(id)), BooleanType)

      // The program with the body of the current function replaced by the current partial solution
      private val (innerProgram, origFdMap) = {

        val outerSolution = {
          new PartialSolution(hctx.search.strat, true)
            .solutionAround(hctx.currentNode)(FunctionInvocation(solFd.typed, p.as.map(_.toVariable)))
            .getOrElse(ctx.reporter.fatalError("Unable to get outer solution"))
        }

        val program0 = addFunDefs(sctx.program, Seq(cTreeFd, solFd, phiFd) ++ outerSolution.defs, hctx.ci.fd)

        cTreeFd.body = None

        solFd.fullBody = Ensuring(
          FunctionInvocation(cTreeFd.typed, p.as.map(_.toVariable)),
          Lambda(p.xs.map(ValDef), p.phi)
        )

        phiFd.body = Some(
          letTuple(p.xs,
                   FunctionInvocation(cTreeFd.typed, p.as.map(_.toVariable)),
                   p.phi)
        )

        replaceFunDefs(program0){
          case fd if fd == hctx.ci.fd =>
            val nfd = fd.duplicate()

            nfd.fullBody = postMap {
              case src if src eq hctx.ci.source =>
                Some(outerSolution.term)

              case _ => None
            }(nfd.fullBody)

            Some(nfd)

          // We freshen/duplicate every functions, except these two as they are
          // fresh anyway and we refer to them directly.
          case `cTreeFd` | `phiFd` | `solFd` =>
            None

          case fd =>
            Some(fd.duplicate())
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

      // The program with the c-tree functions
      private var programCTree: Program = _

      private var evaluator: DefaultEvaluator = _

      // Updates the program with the C tree after recalculating all relevant FunDef's
      private def setCExpr(): Unit = {

        // Computes a Seq of functions corresponding to the choices made at each non-terminal of the grammar,
        // and an expression which calls the top-level one.
        def computeCExpr(): (Expr, Seq[FunDef]) = {
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
            cToFd += c -> new FunDef(FreshIdentifier(c.asString, alwaysShowUniqueID = true), Seq(), p.as.map(id => ValDef(id)), c.getType)
          }

          // Fill C-def bodies
          for ((c, alts) <- cTree) {

            val body = if (alts.nonEmpty) {
              alts.init.foldLeft(exprOf(alts.last)) {
                case (e, alt) => IfExpr(alt._1.toVariable, exprOf(alt), e)
              }
            } else {
              Error(c.getType, s"Empty production rule: $c")
            }

            cToFd(c).fullBody = body
          }

          // Top-level expression for rootC
          val expr = {
            val fd = cToFd(rootC)
            FunctionInvocation(fd.typed, fd.params.map(_.toVariable))
          }

          (expr, cToFd.values.toSeq)
        }


        val (cExpr, newFds) = computeCExpr()

        cTreeFd.body = Some(cExpr)
        programCTree = addFunDefs(innerProgram, newFds, cTreeFd)
        evaluator = new DefaultEvaluator(sctx.context, programCTree)

        //println("-- "*30)
        //println(programCTree.asString)
        //println(".. "*30)
      }

      // Tests a candidate solution against an example in the correct environment
      def testForProgram(bValues: Set[Identifier])(ex: Example): Boolean = {

        def redundant(e: Expr): Boolean = {
          val (op1, op2) = e match {
            case Minus(o1, o2) => (o1, o2)
            case Modulo(o1, o2) => (o1, o2)
            case Division(o1, o2) => (o1, o2)
            case BVMinus(o1, o2) => (o1, o2)
            case BVRemainder(o1, o2) => (o1, o2)
            case BVDivision(o1, o2) => (o1, o2)

            case And(Seq(Not(o1), Not(o2))) => (o1, o2)
            case And(Seq(Not(o1), o2)) => (o1, o2)
            case And(Seq(o1, Not(o2))) => (o1, o2)
            case And(Seq(o1, o2)) => (o1, o2)

            case Or(Seq(Not(o1), Not(o2))) => (o1, o2)
            case Or(Seq(Not(o1), o2)) => (o1, o2)
            case Or(Seq(o1, Not(o2))) => (o1, o2)
            case Or(Seq(o1, o2)) => (o1, o2)

            case SetUnion(o1, o2) => (o1, o2)
            case SetIntersection(o1, o2) => (o1, o2)
            case SetDifference(o1, o2) => (o1, o2)

            case Equals(Not(o1), Not(o2)) => (o1, o2)
            case Equals(Not(o1), o2) => (o1, o2)
            case Equals(o1, Not(o2)) => (o1, o2)
            case Equals(o1, o2) => (o1, o2)
            case _ => return false
          }

          op1 == op2
        }

        val origImpl = cTreeFd.fullBody
        val outerSol = getExpr(bValues)

        val redundancyCheck = false

        // This program contains a simplifiable expression,
        // which means it is equivalent to a simpler one
        // Deactivated for now, since it doesnot seem to help
        if (redundancyCheck && params.optimizations && exists(redundant)(outerSol)) {
          excludeProgram(bs, true)
          return false
        }
        val innerSol = outerExprToInnerExpr(outerSol)
        val cnstr = letTuple(p.xs, innerSol, innerPhi)
        cTreeFd.fullBody = innerSol

        timers.testForProgram.start()
        val res = ex match {
          case InExample(ins) =>
            evaluator.eval(cnstr, p.as.zip(ins).toMap)

          case InOutExample(ins, outs) =>
            val eq = equality(innerSol, tupleWrap(outs))
            evaluator.eval(eq, p.as.zip(ins).toMap)
        }
        timers.testForProgram.stop()

        cTreeFd.fullBody = origImpl

        res match {
          case EvaluationResults.Successful(res) =>
            res == BooleanLiteral(true)

          case EvaluationResults.RuntimeError(err) =>
            /*if (err.contains("Empty production rule")) {
              println(programCTree.asString)
              println(bValues)
              println(ex)
              println(this.getExpr(bValues))
              (new Throwable).printStackTrace()
              println(err)
              println()
            }*/
            sctx.reporter.debug("RE testing CE: "+err)
            false

          case EvaluationResults.EvaluatorError(err) =>
            sctx.reporter.debug("Error testing CE: "+err)
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
            Error(c.getType, "Impossible assignment of bs")
          }
        }

        getCValue(rootC)
      }

      /**
       * Here we check the validity of a (small) number of programs in isolation.
       * We keep track of CEXs generated by invalid programs and preemptively filter the rest of the programs with them.
       */
      def validatePrograms(bss: Set[Set[Identifier]]): Either[Seq[Seq[Expr]], Solution] = {
        val origImpl = cTreeFd.fullBody

        var cexs = Seq[Seq[Expr]]()

        for (bs <- bss.toSeq) {
          // We compute the corresponding expr and replace it in place of the C-tree
          val outerSol = getExpr(bs)
          val innerSol = outerExprToInnerExpr(outerSol)
          //println(s"Testing $outerSol")
          cTreeFd.fullBody = innerSol

          val cnstr = and(innerPc, letTuple(p.xs, innerSol, Not(innerPhi)))

          val eval = new DefaultEvaluator(ctx, innerProgram)

          if (cexs exists (cex => eval.eval(cnstr, p.as.zip(cex).toMap).result == Some(BooleanLiteral(true)))) {
            //println(s"Program $outerSol fails!")
            excludeProgram(bs, true)
            cTreeFd.fullBody = origImpl
          } else {
            //println("Solving for: "+cnstr.asString)

            val solverf = SolverFactory.getFromSettings(ctx, innerProgram).withTimeout(cexSolverTo)
            val solver = solverf.getNewSolver()
            try {
              solver.assertCnstr(cnstr)
              solver.check match {
                case Some(true) =>
                  excludeProgram(bs, true)
                  val model = solver.getModel
                  //println("Found counter example: ")
                  //for ((s, v) <- model) {
                  //  println(" "+s.asString+" -> "+v.asString)
                  //}

                  //val evaluator  = new DefaultEvaluator(ctx, prog)
                  //println(evaluator.eval(cnstr, model))
                  //println(s"Program $outerSol fails with cex ${p.as.map(a => model.getOrElse(a, simplestValue(a.getType)))}")
                  cexs +:= p.as.map(a => model.getOrElse(a, simplestValue(a.getType)))

                case Some(false) =>
                  // UNSAT, valid program
                  return Right(Solution(BooleanLiteral(true), Set(), outerSol, true))

                case None =>
                  if (useOptTimeout) {
                    // Interpret timeout in CE search as "the candidate is valid"
                    sctx.reporter.info("CEGIS could not prove the validity of the resulting expression")
                    // Optimistic valid solution
                    return Right(Solution(BooleanLiteral(true), Set(), outerSol, false))
                  }
              }
            } finally {
              solverf.reclaim(solver)
              solverf.shutdown()
              cTreeFd.fullBody = origImpl
            }
          }
        }

        Left(cexs)
      }

      def allProgramsClosed = prunedPrograms.isEmpty

      // Explicitly remove program computed by bValues from the search space
      //
      // If the bValues comes from models, we make sure the bValues we exclude
      // are minimal we make sure we exclude only Bs that are used.
      def excludeProgram(bs: Set[Identifier], isMinimal: Boolean): Unit = {

        def filterBTree(c: Identifier): Set[Identifier] = {
          (for ((b, _, subcs) <- cTree(c) if bs(b)) yield {
           Set(b) ++ subcs.flatMap(filterBTree)
          }).toSet.flatten
        }

        val bvs = if (isMinimal) {
          bs
        } else {
          filterBTree(rootC)
        }

        excludedPrograms += bvs
        prunedPrograms   -= bvs
      }

      def unfold() = {
        termSize += 1
        updateCTree()
      }

      /**
       * First phase of CEGIS: discover potential programs (that work on at least one input)
       */
      def solveForTentativeProgram(): Option[Option[Set[Identifier]]] = {
        val solverf = SolverFactory.getFromSettings(ctx, programCTree).withTimeout(exSolverTo)
        val solver  = solverf.getNewSolver()
        val cnstr = FunctionInvocation(phiFd.typed, phiFd.params.map(_.id.toVariable))

        //println("Program: ")
        //println("-"*80)
        //println(programCTree.asString)

        val toFind = and(innerPc, cnstr)
        //println(" --- Constraints ---")
        //println(" - "+toFind.asString)
        try {
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

          //println(" -- Excluded:")
          for (ex <- excludedPrograms) {
            val notThisProgram = Not(andJoin(ex.map(_.toVariable).toSeq))

            //println(f"  - ${notThisProgram.asString}%-40s ("+getExpr(ex)+")")
            solver.assertCnstr(notThisProgram)
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
               * If the remaining tentative programs are all infeasible, it
               * might timeout instead of returning Some(false). We might still
               * benefit from unfolding further
               */
              ctx.reporter.debug("Timeout while getting tentative program!")
              Some(None)
          }
        } finally {
          solverf.reclaim(solver)
          solverf.shutdown()
        }
      }

      /**
       * Second phase of CEGIS: verify a given program by looking for CEX inputs
       */
      def solveForCounterExample(bs: Set[Identifier]): Option[Option[Seq[Expr]]] = {
        val solverf = SolverFactory.getFromSettings(ctx, programCTree).withTimeout(cexSolverTo)
        val solver  = solverf.getNewSolver()
        val cnstr = FunctionInvocation(phiFd.typed, phiFd.params.map(_.id.toVariable))


        try {
          solver.assertCnstr(andJoin(bsOrdered.map(b => if (bs(b)) b.toVariable else Not(b.toVariable))))
          solver.assertCnstr(innerPc)
          solver.assertCnstr(Not(cnstr))

          //println("*"*80)
          //println(Not(cnstr))
          //println(innerPc)
          //println("*"*80)
          //println(programCTree.asString)
          //println("*"*80)
          //Console.in.read()

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
          solverf.reclaim(solver)
          solverf.shutdown()
        }
      }
    }

    List(new RuleInstantiation(this.name) {
      def apply(hctx: SearchContext): RuleApplication = {
        var result: Option[RuleApplication] = None
        val sctx = hctx.sctx
        implicit val ctx = sctx.context

        val ndProgram = NonDeterministicProgram
        ndProgram.init()

        sctx.reporter.debug("Acquiring initial list of examples")

        // To the list of known examples, we add an additional one produced by the solver
        val solverExample = if (p.pc == BooleanLiteral(true)) {
          InExample(p.as.map(a => simplestValue(a.getType)))
        } else {
          val solverf = sctx.solverFactory
          val solver  = solverf.getNewSolver().setTimeout(exSolverTo)

          solver.assertCnstr(p.pc)

          try {
            solver.check match {
              case Some(true) =>
                val model = solver.getModel
                InExample(p.as.map(a => model.getOrElse(a, simplestValue(a.getType))))

              case Some(false) =>
                sctx.reporter.debug("Path-condition seems UNSAT")
                return RuleFailed()

              case None =>
                if (!interruptManager.isInterrupted) {
                  sctx.reporter.warning("Solver could not solve path-condition")
                }
                return RuleFailed() // This is not necessary though, but probably wanted
            }
          } finally {
            solverf.reclaim(solver)
          }
        }

        val baseExampleInputs = p.eb.examples :+ solverExample

        sctx.reporter.ifDebug { debug =>
          baseExampleInputs.foreach { in =>
            debug("  - "+in.asString)
          }
        }

        /**
         * We (lazily) generate additional tests for discarding potential programs with a data generator
         */
        val nTests = if (p.pc == BooleanLiteral(true)) 50 else 20

        val inputGenerator: Iterator[Example] = if (useVanuatoo) {
          new VanuatooDataGen(sctx.context, sctx.program).generateFor(p.as, p.pc, nTests, 3000).map(InExample)
        } else {
          val evaluator = new DualEvaluator(sctx.context, sctx.program, CodeGenParams.default)
          new GrammarDataGen(evaluator, ValueGrammar).generateFor(p.as, p.pc, nTests, 1000).map(InExample)
        }

        // This is the starting test-base
        val gi = new GrowableIterable[Example](baseExampleInputs, inputGenerator)

        // We keep number of failures per test to pull the better ones to the front
        val failedTestsStats = new MutableMap[Example, Int]().withDefaultValue(0)

        def hasInputExamples = gi.nonEmpty

        var n = 1
        def allInputExamples() = {
          if (n == 10 || n == 50 || n % 500 == 0) {
            gi.sortBufferBy(e => -failedTestsStats(e))
          }
          n += 1
          gi.iterator
        }

        try {
          do {
            // Run CEGIS for one specific unfolding level

            // Unfold formula
            ndProgram.unfold()

            val nInitial = ndProgram.prunedPrograms.size
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

            // We further filter the set of working programs to remove those that fail on known examples
            if (hasInputExamples) {
              timers.filter.start()
              for (bs <- ndProgram.prunedPrograms if !interruptManager.isInterrupted) {
                val examples = allInputExamples()
                examples.find(e => !ndProgram.testForProgram(bs)(e)).foreach { e =>
                  failedTestsStats(e) += 1
                  sctx.reporter.debug(f" Program: ${ndProgram.getExpr(bs).asString}%-80s failed on: ${e.asString}")
                  ndProgram.excludeProgram(bs, true)
                }

                if (ndProgram.excludedPrograms.size+1 % 1000 == 0) {
                  sctx.reporter.debug("..."+ndProgram.excludedPrograms.size)
                }
              }
              timers.filter.stop()
            }

            def nPassing = ndProgram.prunedPrograms.size

            sctx.reporter.debug(s"#Programs passing tests: $nPassing out of $nInitial")
            sctx.reporter.ifDebug{ printer =>
              for (p <- ndProgram.prunedPrograms.take(100)) {
                printer(" - "+ndProgram.getExpr(p).asString)
              }
              if(nPassing > 100) {
                printer(" - ...")
              }
            }
            sctx.reporter.debug("#Tests: "+baseExampleInputs.size)
            sctx.reporter.ifDebug{ printer =>
              for (e <- baseExampleInputs.take(10)) {
                printer(" - "+e.asString)
              }
              if(baseExampleInputs.size > 10) {
                printer(" - ...")
              }
            }

            // CEGIS Loop at a given unfolding level
            while (result.isEmpty && !interruptManager.isInterrupted && !ndProgram.allProgramsClosed) {
              timers.loop.start()
              ctx.reporter.debug("Programs left: " + ndProgram.prunedPrograms.size)

              // Phase 0: If the number of remaining programs is small, validate them individually
              if (nInitial / nPassing > testReductionRatio || nPassing <= 10) {
                val programsToValidate = ndProgram.prunedPrograms
                sctx.reporter.debug(s"Will send ${programsToValidate.size} program(s) to validate individually")
                ndProgram.validatePrograms(programsToValidate) match {
                  case Right(sol) =>
                    // Found solution! Exit CEGIS
                    result = Some(RuleClosed(sol))
                  case Left(cexs) =>
                    // Found some counterexamples
                    // (bear in mind that these will in fact exclude programs within validatePrograms()
                    val newCexs = cexs.map(InExample)
                    gi ++= newCexs
                }
                ctx.reporter.debug(s"#Programs after validating individually: ${ndProgram.prunedPrograms.size}")
              }

              if (result.isEmpty && !ndProgram.allProgramsClosed) {
                // Phase 1: Find a candidate program that works for at least 1 input
                ndProgram.solveForTentativeProgram() match {
                  case Some(Some(bs)) =>
                    sctx.reporter.debug(s"Found tentative model ${ndProgram.getExpr(bs)}, need to validate!")
                    // Phase 2: Validate candidate model
                    ndProgram.solveForCounterExample(bs) match {
                      case Some(Some(inputsCE)) =>
                        sctx.reporter.debug("Found counter-example:" + inputsCE)
                        val ce = InExample(inputsCE)
                        // Found counterexample! Exclude this program
                        gi += ce
                        failedTestsStats(ce) += 1
                        ndProgram.excludeProgram(bs, false)

                        // Retest whether the newly found C-E invalidates some programs
                        ndProgram.prunedPrograms.foreach { p =>
                          if (!ndProgram.testForProgram(p)(ce)) {
                            failedTestsStats(ce) += 1
                            ndProgram.excludeProgram(p, true)
                          }
                        }

                      case Some(None) =>
                        // Found no counter example! Program is a valid solution
                        val expr = ndProgram.getExpr(bs)
                        result = Some(RuleClosed(Solution(BooleanLiteral(true), Set(), expr)))

                      case None =>
                        // We are not sure
                        sctx.reporter.debug("Unknown")
                        if (useOptTimeout) {
                          // Interpret timeout in CE search as "the candidate is valid"
                          sctx.reporter.info("CEGIS could not prove the validity of the resulting expression")
                          val expr = ndProgram.getExpr(bs)
                          result = Some(RuleClosed(Solution(BooleanLiteral(true), Set(), expr, isTrusted = false)))
                        } else {
                          // Ok, we failed to validate, exclude this program
                          ndProgram.excludeProgram(bs, false)
                          // TODO: Make CEGIS fail early when it fails on 1 program?
                          // result = Some(RuleFailed())
                        }
                    }

                  case Some(None) =>
                    sctx.reporter.debug("There exists no candidate program!")
                    ndProgram.prunedPrograms foreach (ndProgram.excludeProgram(_, true))

                  case None =>
                    result = Some(RuleFailed())
                }
              }
              timers.loop.stop()
            }

          } while(ndProgram.unfolding < maxSize && result.isEmpty && !interruptManager.isInterrupted)

          if (interruptManager.isInterrupted) interruptManager.recoverInterrupt()
          result.getOrElse(RuleFailed())

        } catch {
          case e: Throwable =>
            sctx.reporter.warning("CEGIS crashed: "+e.getMessage)
            e.printStackTrace()
            RuleFailed()
        }
      }
    })
  }
}
