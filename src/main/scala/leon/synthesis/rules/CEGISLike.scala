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

import solvers._
import grammars._
import grammars.aspects._
import leon.utils._

import evaluators._
import datagen._
import codegen.CodeGenParams

import scala.collection.mutable.{HashMap => MutableMap}

abstract class CEGISLike(name: String) extends Rule(name) {

  case class CegisParams(
    grammar: ExpressionGrammar,
    rootLabel: TypeTree => Label,
    optimizations: Boolean,
    maxSize: Option[Int] = None
  )

  def getParams(sctx: SynthesisContext, p: Problem): CegisParams

  def instantiateOn(implicit hctx: SearchContext, p: Problem): Traversable[RuleInstantiation] = {

    import hctx.reporter._

    val exSolverTo  = 500L
    val cexSolverTo = 3000L

    // Track non-deterministic programs up to 100'000 programs, or give up
    val nProgramsLimit = 100000

    val timers = hctx.timers.synthesis.applications.CEGIS

    // CEGIS Flags to activate or deactivate features
    val useOptTimeout = hctx.settings.cegisUseOptTimeout
    val useVanuatoo   = hctx.settings.cegisUseVanuatoo

    // The factor by which programs need to be reduced by testing before we validate them individually
    val testReductionRatio = 10

    val interruptManager = hctx.interruptManager

    val params = getParams(hctx, p)

    // If this CEGISLike forces a maxSize, take it, otherwise find it in the settings
    val maxSize = params.maxSize.getOrElse(hctx.settings.cegisMaxSize)

    if (maxSize == 0) {
      return Nil
    }

    // Represents a non-deterministic program
    object NonDeterministicProgram {

      // Current synthesized term size
      private var termSize = 0

      def unfolding = termSize

      private val targetType = tupleTypeWrap(p.xs.map(_.getType))

      val grammar = params.grammar

      def rootLabel = params.rootLabel(targetType).withAspect(TypeDepthBound(depth(targetType) + 1)).withAspect(Sized(termSize))

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

      // Programs we have manually excluded
      var excludedPrograms = Set[Set[Identifier]]()
      // Still live programs (allPrograms -- excludedPrograms)
      var prunedPrograms   = Set[Set[Identifier]]()

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
        setCExpr()

        excludedPrograms = Set()
        prunedPrograms = allPrograms().toSet

        timers.updateCTree.stop()
      }

      // Returns a count of all possible programs
      val allProgramsCount: () => Int = {
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
      def allPrograms(): Traversable[Set[Identifier]] = {

        var cache = Map[Identifier, Seq[Set[Identifier]]]()

        val c = allProgramsCount()

        if (c > nProgramsLimit) {
          debug(s"Exceeded program limit: $c > $nProgramsLimit")
          return Seq()
        }

        def allProgramsFor(c: Identifier): Seq[Set[Identifier]] = {
          if (!(cache contains c)) {
            val subs = for ((b, _, subcs) <- cTree(c)) yield {
              if (subcs.isEmpty) {
                Seq(Set(b))
              } else {
                val subPs = subcs map (s => allProgramsFor(s))
                val combos = SeqUtils.cartesianProduct(subPs).map(_.flatten.toSet)
                combos map (_ + b)
              }
            }
            cache += c -> subs.flatten
          }
          cache(c)
        }

        allProgramsFor(rootC)

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

      // The spec of the problem
      private val phiFd = new FunDef(FreshIdentifier("phiFd", alwaysShowUniqueID = true), Seq(), p.as.map(id => ValDef(id)), BooleanType)

      // The program with the body of the current function replaced by the current partial solution
      private val (innerProgram, origIdMap, origFdMap, origCdMap) = {

        val outerSolution = {
          new PartialSolution(hctx.search.strat, true)
            .solutionAround(hctx.currentNode)(FunctionInvocation(cTreeFd.typed, p.as.map(_.toVariable)))
            .getOrElse(fatalError("Unable to get outer solution"))
        }

        val program0 = addFunDefs(hctx.program, Seq(cTreeFd, phiFd) ++ outerSolution.defs, hctx.functionContext)

        cTreeFd.body = None

        phiFd.body = Some(
          letTuple(p.xs,
                   FunctionInvocation(cTreeFd.typed, p.as.map(_.toVariable)),
                   p.phi)
        )

        replaceFunDefs(program0){
          case fd if fd == hctx.functionContext =>
            val nfd = fd.duplicate()

            nfd.fullBody = postMap {
              case src if src eq hctx.source =>
                Some(outerSolution.term)

              case _ => None
            }(nfd.fullBody)

            Some(nfd)

          // We freshen/duplicate every functions, except these two as they are
          // fresh anyway and we refer to them directly.
          case `cTreeFd` | `phiFd` =>
            None

          case fd =>
            Some(fd.duplicate())
        }
      }

      private val outerToInner = new purescala.TreeTransformer {
        override def transform(id: Identifier): Identifier = origIdMap.getOrElse(id, id)
        override def transform(cd: ClassDef): ClassDef = origCdMap.getOrElse(cd, cd)
        override def transform(fd: FunDef): FunDef = origFdMap.getOrElse(fd, fd)
      }

      /**
       * Since CEGIS works with a copy of the program, it needs to map outer
       * function calls to inner function calls and vice-versa. 'inner' refers
       * to the CEGIS-specific program, 'outer' refers to the actual program on
       * which we do synthesis.
       */
      private def outerExprToInnerExpr(e: Expr): Expr = outerToInner.transform(e)(Map.empty)

      private val innerPc  = p.pc map outerExprToInnerExpr
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
              fd.applied
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
            fd.applied
          }

          (expr, cToFd.values.toSeq)
        }


        val (cExpr, newFds) = computeCExpr()

        cTreeFd.body = Some(cExpr)
        programCTree = addFunDefs(innerProgram, newFds, cTreeFd)
        evaluator = new DefaultEvaluator(hctx, programCTree)

        //println("-- "*30)
        //println(programCTree.asString)
        //println(".. "*30)
      }

      // Tests a candidate solution against an example in the correct environment
      // None -> evaluator error
      def testForProgram(bValues: Set[Identifier])(ex: Example): Option[Boolean] = {

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
        // Deactivated for now, since it does not seem to help
        if (redundancyCheck && params.optimizations && exists(redundant)(outerSol)) {
          excludeProgram(bs, true)
          return Some(false)
        }
        val innerSol = outerExprToInnerExpr(outerSol)
        val cnstr = letTuple(p.xs, innerSol, innerPhi)

        def withBindings(e: Expr) = p.pc.bindings.foldRight(e){
          case ((id, v), bd) => let(id, outerExprToInnerExpr(v), bd)
        }

        cTreeFd.fullBody = withBindings(innerSol) // FIXME! This shouldnt be needed... Solution around should be somehow used

        timers.testForProgram.start()

        val boundCnstr = withBindings(cnstr)

        val res = ex match {
          case InExample(ins) =>
            evaluator.eval(boundCnstr, p.as.zip(ex.ins).toMap)

          case InOutExample(ins, outs) =>
            evaluator.eval(
              withBindings(equality(innerSol, tupleWrap(outs))),
              p.as.zip(ex.ins).toMap
            )
        }
        timers.testForProgram.stop()

        cTreeFd.fullBody = origImpl

        res match {
          case EvaluationResults.Successful(res) =>
            Some(res == BooleanLiteral(true))

          case EvaluationResults.RuntimeError(err) =>
            debug("RE testing CE: "+err)
            Some(false)

          case EvaluationResults.EvaluatorError(err) =>
            debug("Error testing CE: "+err)
            //println(s"InnerSol: $innerSol")
            //println(s"Constr  : $boundCnstr")
            None
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
      def validatePrograms(bss: Set[Set[Identifier]]): Either[Seq[Seq[Expr]], Stream[Solution]] = {
        val origImpl = cTreeFd.fullBody

        var cexs = Seq[Seq[Expr]]()

        var best: List[Solution] = Nil

        for (bs <- bss.toSeq) {
          // We compute the corresponding expr and replace it in place of the C-tree
          val outerSol = getExpr(bs)
          val innerSol = outerExprToInnerExpr(outerSol)
          //println(s"Testing $innerSol")
          //println(innerProgram)
          cTreeFd.fullBody = innerSol

          val cnstr = innerPc and letTuple(p.xs, innerSol, Not(innerPhi))

          val eval = new DefaultEvaluator(hctx, innerProgram)

          if (cexs exists (cex => eval.eval(cnstr, p.as.zip(cex).toMap).result == Some(BooleanLiteral(true)))) {
            debug(s"Rejected by CEX: $outerSol")
            excludeProgram(bs, true)
            cTreeFd.fullBody = origImpl
          } else {
            //println("Solving for: "+cnstr.asString)

            val solverf = SolverFactory.getFromSettings(hctx, innerProgram).withTimeout(cexSolverTo)
            val solver = solverf.getNewSolver()
            try {
              debug("Sending candidate to solver...")
              def currentSolution(trusted: Boolean) = Solution(BooleanLiteral(true), Set(), outerSol, isTrusted = trusted)
              solver.assertCnstr(cnstr)
              solver.check match {
                case Some(true) =>
                  debug(s"Proven invalid: $outerSol")
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
                  debug("Found valid program!")
                  return Right(Stream(currentSolution(true)))

                case None =>
                  debug("Found a non-verifiable solution...")
                  // Optimistic valid solution
                  best +:= currentSolution(false)
              }
            } finally {
              solverf.reclaim(solver)
              solverf.shutdown()
              cTreeFd.fullBody = origImpl
            }
          }
        }

        if (useOptTimeout && best.nonEmpty) {
          // Interpret timeout in CE search as "the candidate is valid"
          info(s"CEGIS could not prove the validity of the resulting ${best.size} expression(s)")
          Right(best.toStream)
        } else {
          Left(cexs)
        }
      }

      def allProgramsClosed = prunedPrograms.isEmpty
      def closeAllPrograms() = {
        excludedPrograms ++= prunedPrograms
        prunedPrograms = Set()
      }

      // Explicitly remove program computed by bValues from the search space
      //
      // If the bValues comes from models, we make sure the bValues we exclude
      // are minimal we make sure we exclude only Bs that are used.
      def excludeProgram(bs: Set[Identifier], isMinimal: Boolean): Unit = {

        def filterBTree(c: Identifier): Set[Identifier] = {
          val (b, _, subcs) = cTree(c).find(sub => bs(sub._1)).get
          subcs.flatMap(filterBTree).toSet + b
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
        timers.tentative.start()
        val solverf = SolverFactory.getFromSettings(hctx, programCTree).withTimeout(exSolverTo)
        val solver  = solverf.getNewSolver()
        val cnstr = phiFd.applied

        //println("Program: ")
        //println("-"*80)
        //println(programCTree.asString)

        val toFind = innerPc and cnstr
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
              None
          }
        } finally {
          timers.tentative.stop()
          solverf.reclaim(solver)
          solverf.shutdown()
        }
      }

      /**
       * Second phase of CEGIS: verify a given program by looking for CEX inputs
       */
      def solveForCounterExample(bs: Set[Identifier]): Option[Option[Seq[Expr]]] = {
        timers.cex.start()
        val solverf = SolverFactory.getFromSettings(hctx, programCTree).withTimeout(cexSolverTo)
        val solver  = solverf.getNewSolver()
        val cnstr   = FunctionInvocation(phiFd.typed, phiFd.params.map(_.id.toVariable))

        try {
          solver.assertCnstr(andJoin(bsOrdered.map(b => if (bs(b)) b.toVariable else Not(b.toVariable))))
          solver.assertCnstr(innerPc and not(cnstr))

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
          timers.cex.stop()
          solverf.reclaim(solver)
          solverf.shutdown()
        }
      }
    }

    List(new RuleInstantiation(this.name) {
      def apply(hctx: SearchContext): RuleApplication = {
        var result: Option[RuleApplication] = None

        val ndProgram = NonDeterministicProgram
        ndProgram.init()

        implicit val ic = hctx

        debug("Acquiring initial list of examples")

        // To the list of known examples, we add an additional one produced by the solver
        val solverExample = if (p.pc.isEmpty) {
          List(InExample(p.as.map(a => simplestValue(a.getType))))
        } else {
          val solverf = hctx.solverFactory
          val solver  = solverf.getNewSolver().setTimeout(exSolverTo)

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
                Nil
                //return RuleFailed() // This is not necessary though, but probably wanted
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

        /**
         * We (lazily) generate additional tests for discarding potential programs with a data generator
         */
        val nTests = if (p.pc.isEmpty) 50 else 20

        val inputGenerator: Iterator[Example] = {
          val complicated = exists{
            case FunctionInvocation(tfd, _) if tfd.fd == hctx.functionContext => true
            case Choose(_) => true
            case _ => false
          }(p.pc.toClause)

          if (complicated) {
            Iterator()
          } else {
            if (useVanuatoo) {
              new VanuatooDataGen(hctx, hctx.program).generateFor(p.as, p.pc.toClause, nTests, 3000).map(InExample)
            } else {
              val evaluator = new DualEvaluator(hctx, hctx.program)
              new GrammarDataGen(evaluator, ValueGrammar).generateFor(p.as, p.pc.toClause, nTests, 1000).map(InExample)
            }
          }
        }

        // We keep number of failures per test to pull the better ones to the front
        val failedTestsStats = new MutableMap[Example, Int]().withDefaultValue(0)

        // This is the starting test-base
        val gi = new GrowableIterable[Example](baseExampleInputs, inputGenerator)
        def hasInputExamples = gi.nonEmpty

        var n = 1

        try {
          do {
            // Run CEGIS for one specific unfolding level

            // Unfold formula
            ndProgram.unfold()

            val nInitial = ndProgram.prunedPrograms.size
            debug(s"#Programs: $nInitial")

            def nPassing = ndProgram.prunedPrograms.size

            def programsReduced() = nPassing <= 10 || (nPassing <= 100 && nInitial / nPassing > testReductionRatio)
            gi.canGrow = programsReduced

            def allInputExamples() = {
              if (n == 10 || n == 50 || n % 500 == 0) {
                gi.sortBufferBy(e => -failedTestsStats(e))
              }
              n += 1
              gi.iterator
            }

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
    
            debug(s"#Tests: >= ${gi.bufferedCount}")
            ifDebug{ printer =>
              val es = allInputExamples()
              for (e <- es.take(Math.min(gi.bufferedCount, 10))) {
                printer(" - "+e.asString)
              }
              if(es.hasNext) {
                printer(" - ...")
              }
            }

            // We further filter the set of working programs to remove those that fail on known examples
            if (hasInputExamples) {
              timers.filter.start()
              for (bs <- ndProgram.prunedPrograms if !interruptManager.isInterrupted) {
                val examples = allInputExamples()
                var badExamples = List[Example]()
                var stop = false
                for (e <- examples if !stop && !badExamples.contains(e)) {
                  ndProgram.testForProgram(bs)(e) match {
                    case Some(true) => // ok, passes
                    case Some(false) =>
                      // Program fails the test
                      stop = true
                      failedTestsStats(e) += 1
                      debug(f" Program: ${ndProgram.getExpr(bs).asString}%-80s failed on: ${e.asString}")
                      ndProgram.excludeProgram(bs, true)
                    case None =>
                      // Eval. error -> bad example
                      debug(s" Test $e crashed the evaluator, removing...")
                      badExamples ::= e
                  }
                }
                gi --= badExamples
              }
              timers.filter.stop()
            }

            debug(s"#Programs passing tests: $nPassing out of $nInitial")
            ifDebug{ printer =>
              for (p <- ndProgram.prunedPrograms.take(100)) {
                printer(" - "+ndProgram.getExpr(p).asString)
              }
              if(nPassing > 100) {
                printer(" - ...")
              }
            }
              // CEGIS Loop at a given unfolding level
            while (result.isEmpty && !interruptManager.isInterrupted && !ndProgram.allProgramsClosed) {
              debug("Programs left: " + ndProgram.prunedPrograms.size)

              // Phase 0: If the number of remaining programs is small, validate them individually
              if (programsReduced()) {
                timers.validate.start()
                val programsToValidate = ndProgram.prunedPrograms
                debug(s"Will send ${programsToValidate.size} program(s) to validate individually")
                ndProgram.validatePrograms(programsToValidate) match {
                  case Right(sols) =>
                    // Found solution! Exit CEGIS
                    result = Some(RuleClosed(sols))
                  case Left(cexs) =>
                    debug(s"Found cexs! $cexs")
                    // Found some counterexamples
                    // (bear in mind that these will in fact exclude programs within validatePrograms())
                    val newCexs = cexs.map(InExample)
                    newCexs foreach (failedTestsStats(_) += 1)
                    gi ++= newCexs
                }
                debug(s"#Programs after validating individually: ${ndProgram.prunedPrograms.size}")
                timers.validate.stop()
              }

              if (result.isEmpty && !ndProgram.allProgramsClosed) {
                // Phase 1: Find a candidate program that works for at least 1 input
                debug("Looking for program that works on at least 1 input...")
                ndProgram.solveForTentativeProgram() match {
                  case Some(Some(bs)) =>
                    debug(s"Found tentative model ${ndProgram.getExpr(bs)}, need to validate!")
                    // Phase 2: Validate candidate model
                    ndProgram.solveForCounterExample(bs) match {
                      case Some(Some(inputsCE)) =>
                        debug("Found counter-example:" + inputsCE)
                        val ce = InExample(inputsCE)
                        // Found counterexample! Exclude this program
                        gi += ce
                        failedTestsStats(ce) += 1
                        ndProgram.excludeProgram(bs, false)

                        var bad = false
                        // Retest whether the newly found C-E invalidates some programs
                        for (p <- ndProgram.prunedPrograms if !bad) {
                          ndProgram.testForProgram(p)(ce) match {
                            case Some(true) =>
                            case Some(false) =>
                              debug(f" Program: ${ndProgram.getExpr(p).asString}%-80s failed on: ${ce.asString}")
                              failedTestsStats(ce) += 1
                              ndProgram.excludeProgram(p, true)
                            case None =>
                              debug(s" Test $ce failed, removing...")
                              gi -= ce
                              bad = true
                          }
                        }

                      case Some(None) =>
                        // Found no counter example! Program is a valid solution
                        val expr = ndProgram.getExpr(bs)
                        result = Some(RuleClosed(Solution(BooleanLiteral(true), Set(), expr)))

                      case None =>
                        // We are not sure
                        debug("Unknown")
                        if (useOptTimeout) {
                          // Interpret timeout in CE search as "the candidate is valid"
                          info("CEGIS could not prove the validity of the resulting expression")
                          val expr = ndProgram.getExpr(bs)
                          result = Some(RuleClosed(Solution(BooleanLiteral(true), Set(), expr, isTrusted = false)))
                        } else {
                          // Ok, we failed to validate, exclude this program
                          ndProgram.excludeProgram(bs, false)
                          // TODO: Make CEGIS fail early when it times out when verifying 1 program?
                          // result = Some(RuleFailed())
                        }
                    }

                  case Some(None) =>
                    debug("There exists no candidate program!")
                    ndProgram.closeAllPrograms()

                  case None =>
                    debug("Timeout while getting tentative program!")
                    ndProgram.closeAllPrograms()
                    // TODO: Make CEGIS fail early when it times out when looking for tentative program?
                    //result = Some(RuleFailed())
                }
              }
            }

          } while(ndProgram.unfolding < maxSize && result.isEmpty && !interruptManager.isInterrupted)

          if (interruptManager.isInterrupted) interruptManager.recoverInterrupt()
          result.getOrElse(RuleFailed())

        } catch {
          case e: Throwable =>
            warning("CEGIS crashed: "+e.getMessage)
            e.printStackTrace()
            RuleFailed()
        }
      }
    })
  }
}
