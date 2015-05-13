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

abstract class CEGISLike[T <% Typed](name: String) extends Rule(name) {

  case class CegisParams(
    grammar: ExpressionGrammar[T],
    rootLabel: TypeTree => T,
    maxUnfoldings: Int = 3
  )

  def getParams(sctx: SynthesisContext, p: Problem): CegisParams

  def instantiateOn(implicit hctx: SearchContext, p: Problem): Traversable[RuleInstantiation] = {
    val exSolverTo  = 2000L
    val cexSolverTo = 2000L

    // Track non-deterministic programs up to 50'000 programs, or give up
    val nProgramsLimit = 100000

    val sctx = hctx.sctx
    val ctx  = sctx.context

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

    class NonDeterministicProgram(val p: Problem) {

      private val grammar = params.grammar

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
      private var cTree: Map[Identifier, Seq[(Identifier, Expr, Set[Identifier])]] = Map()

      /**
       * Computes dependencies of c's
       *
       * c1 -> Set(c2, c3, c4, c5)
       */
      private var cDeps: Map[Identifier, Set[Identifier]] = Map()

      /**
       * Keeps track of blocked Bs and which C are affected, assuming cs are undefined:
       *
       * b2 -> Set(c4)
       * b3 -> Set(c4)
       */
      private var closedBs: Map[Identifier, Set[Identifier]] = Map()

      /**
       * Maps c identifiers to grammar labels
       *
       * Labels allows us to use grammars that are not only type-based
       */
      private var labels: Map[Identifier, T] = Map() ++ p.xs.map(x => x -> params.rootLabel(x.getType))

      private var bs: Set[Identifier]        = Set()
      private var bsOrdered: Seq[Identifier] = Seq()

      /**
       * Checks if 'b' is closed (meaning it depends on uninterpreted terms)
       */
      def isBActive(b: Identifier) = !closedBs.contains(b)


      def allProgramsCount(): Int = {
        var nAltsCache = Map[Identifier, Int]()

        def nAltsFor(c: Identifier): Int = {
          if (!(nAltsCache contains c)) {
            val subs = for ((b, _, subcs) <- cTree(c) if isBActive(b)) yield {
              if (subcs.isEmpty) {
                1
              } else {
                subcs.toSeq.map(nAltsFor).product
              }
            }

            nAltsCache += c -> subs.sum
          }
          nAltsCache(c)
        }

        p.xs.map(nAltsFor).product
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

        def allProgramsFor(cs: Set[Identifier]): Seq[Set[Identifier]] = {
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

        allProgramsFor(p.xs.toSet)
      }

      private def debugCExpr(cTree: Map[Identifier, Seq[(Identifier, Expr, Set[Identifier])]],
                             markedBs: Set[Identifier] = Set()): Unit = {
        println(" -- -- -- -- -- ")
        for ((c, alts) <- cTree) {
          println
          println(f"$c%-4s :=")
          for ((b, ex, cs) <- alts ) {
            val active = if (isBActive(b)) " " else "⨯"
            val markS   = if (markedBs(b)) Console.GREEN else ""
            val markE   = if (markedBs(b)) Console.RESET else ""

            println(f"      $markS$active  $b%-4s => $ex%-40s [$cs]$markE")
          }
        }
      }

      private def computeCExpr(): Expr = {

        val lets = for ((c, alts) <- cTree) yield {
          val activeAlts = alts.filter(a => isBActive(a._1))

          val expr = activeAlts.foldLeft(simplestValue(c.getType): Expr) {
            case (e, (b, ex, _)) => IfExpr(b.toVariable, ex, e)
          }

          (c, expr)
        }

        // We order the lets base don dependencies
        def defFor(c: Identifier): Expr = {
          cDeps(c).filter(lets.contains).foldLeft(lets(c)) {
            case (e, c) => Let(c, defFor(c), e)
          }
        }

        val res = tupleWrap(p.xs.map(defFor))

        val substMap : Map[Expr,Expr] = bsOrdered.zipWithIndex.map {
          case (b, i) => Variable(b) -> ArraySelect(bArrayId.toVariable, IntLiteral(i))
        }.toMap

        val simplerRes = simplifyLets(res)

        replace(substMap, simplerRes)
      }


      /**
       * Information about the final Program representing CEGIS solutions at
       * the current unfolding level
       */
      private val outerSolution = {
        val part = new PartialSolution(hctx.search.g, true)
        e : Expr => part.solutionAround(hctx.currentNode)(e).getOrElse {
          sctx.reporter.fatalError("Unable to create outer solution")
        }
      }

      private val bArrayId = FreshIdentifier("bArray", ArrayType(BooleanType), true)

      private var cTreeFd = new FunDef(FreshIdentifier("cTree", alwaysShowUniqueID = true),
                               Seq(),
                               p.outType,
                               p.as.map(id => ValDef(id)),
                               DefType.MethodDef
                             )

      private var phiFd   = new FunDef(FreshIdentifier("phiFd", alwaysShowUniqueID = true),
                               Seq(),
                               BooleanType,
                               p.as.map(id => ValDef(id)),
                               DefType.MethodDef
                             )

      private var programCTree: Program = _

      // Map functions from original program to cTree program
      private var fdMapCTree: Map[FunDef, FunDef] = _

      private var tester: (Seq[Expr], Set[Identifier]) => EvaluationResults.Result = _

      private def initializeCTreeProgram(): Unit = {

        // CEGIS is solved by called cTree function (without bs yet)
        val fullSol = outerSolution(FunctionInvocation(cTreeFd.typed, p.as.map(_.toVariable)))


        val chFd = hctx.ci.fd
        val prog0 = hctx.program

        val affected = prog0.callGraph.transitiveCallers(chFd) ++ Set(chFd, cTreeFd, phiFd) ++ fullSol.defs

        cTreeFd.body = None
        phiFd.body   = Some(
          letTuple(p.xs,
                   FunctionInvocation(cTreeFd.typed, p.as.map(_.toVariable)),
                   p.phi)
        )

        val prog1 = addFunDefs(prog0, Seq(cTreeFd, phiFd) ++ fullSol.defs, chFd)

        val (prog2, fdMap2) = replaceFunDefs(prog1)({
          case fd if affected(fd) =>
            // Add the b array argument to all affected functions
            val nfd = new FunDef(fd.id.freshen,
                                 fd.tparams,
                                 fd.returnType,
                                 fd.params :+ ValDef(bArrayId),
                                 fd.defType)
            nfd.copyContentFrom(fd)
            nfd.copiedFrom(fd)

            if (fd == chFd) {
              nfd.fullBody = replace(Map(hctx.ci.ch -> fullSol.guardedTerm), nfd.fullBody)
            }

            Some(nfd)

          case _ =>
            None
        }, {
          case (FunctionInvocation(old, args), newfd) if old.fd != newfd =>
            Some(FunctionInvocation(newfd.typed(old.tps), args :+ bArrayId.toVariable))
          case _ =>
            None
        })

        programCTree = prog2
        cTreeFd      = fdMap2(cTreeFd)
        phiFd        = fdMap2(phiFd)
        fdMapCTree   = fdMap2
      }

      private def setCExpr(cTree: Expr): Unit = {

        cTreeFd.body = Some(preMap{
          case FunctionInvocation(TypedFunDef(fd, tps), args) if fdMapCTree contains fd =>
            Some(FunctionInvocation(fdMapCTree(fd).typed(tps), args :+ bArrayId.toVariable))
          case _ =>
            None
        }(cTree))

        //println("-- "*30)
        //println(programCTree)
        //println(".. "*30)

        val evaluator  = new DualEvaluator(sctx.context, programCTree, CodeGenParams.default)


        tester =
          { (ins: Seq[Expr], bValues: Set[Identifier]) =>
            val bsValue = finiteArray(bsOrdered.map(b => BooleanLiteral(bValues(b))), None, BooleanType)
            val args = ins :+ bsValue

            val fi = FunctionInvocation(phiFd.typed, args)

            evaluator.eval(fi, Map())
          }
      }


      private def updateCTree() {
        if (programCTree eq null) {
          initializeCTreeProgram()
        }

        setCExpr(computeCExpr())
      }

      def testForProgram(bValues: Set[Identifier])(ins: Seq[Expr]): Boolean = {
        tester(ins, bValues) match {
          case EvaluationResults.Successful(res) =>
            res == BooleanLiteral(true)

          case EvaluationResults.RuntimeError(err) =>
            false

          case EvaluationResults.EvaluatorError(err) =>
            sctx.reporter.error("Error testing CE: "+err)
            false
        }
      }



      def getExpr(bValues: Set[Identifier]): Expr = {
        def getCValue(c: Identifier): Expr = {
          cTree(c).find(i => bValues(i._1)).map {
            case (b, ex, cs) =>
              val map = for (c <- cs) yield {
                c -> getCValue(c)
              }

              substAll(map.toMap, ex)
          }.getOrElse {
            simplestValue(c.getType)
          }
        }

        tupleWrap(p.xs.map(c => getCValue(c)))
      }

      def validatePrograms(bss: Set[Set[Identifier]]): Either[Stream[Solution], Seq[Seq[Expr]]] = {
        try {
          val cexs = for (bs <- bss.toSeq) yield {
            val sol = getExpr(bs)

            val fullSol = outerSolution(sol)

            val prog = addFunDefs(hctx.program, fullSol.defs, hctx.ci.fd)

            hctx.ci.ch.impl = Some(fullSol.guardedTerm)

            val cnstr = and(p.pc, letTuple(p.xs, sol, Not(p.phi)))
            //println("Solving for: "+cnstr)

            val solverf = SolverFactory.default(ctx, prog).withTimeout(cexSolverTo)
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
                  return Left(Stream(Solution(BooleanLiteral(true), Set(), sol, true)))

                case None =>
                  if (useOptTimeout) {
                    // Interpret timeout in CE search as "the candidate is valid"
                    sctx.reporter.info("CEGIS could not prove the validity of the resulting expression")
                    // Optimistic valid solution
                    return Left(Stream(Solution(BooleanLiteral(true), Set(), sol, false)))
                  } else {
                    None
                  }
              }
            } finally {
              solver.free()
              solverf.shutdown()
            }
          }

          Right(cexs.flatten)
        } finally {
          hctx.ci.ch.impl = None
        }
      }

      var excludedPrograms = ArrayBuffer[Set[Identifier]]()

      // Explicitly remove program computed by bValues from the search space
      def excludeProgram(bValues: Set[Identifier]): Unit = {
        val bvs = bValues.filter(isBActive)
        //println(f" (-)  ${bvs.mkString(", ")}%-40s  ("+getExpr(bvs)+")")
        excludedPrograms += bvs
      }

      /**
       * Shrinks the non-deterministic program to the provided set of
       * alternatives only
       */
      def shrinkTo(remainingBs: Set[Identifier], finalUnfolding: Boolean): Unit = {
        //println("Shrinking!")

        val initialBs = remainingBs ++ (if (finalUnfolding) Set() else closedBs.keySet)

        var cParent = Map[Identifier, Identifier]()
        var cOfB    = Map[Identifier, Identifier]()
        var underBs = Map[Identifier, Set[Identifier]]()

        for ((cparent, alts) <- cTree;
             (b, _, cs) <- alts) {

          cOfB += b -> cparent

          for (cchild <- cs) {
            underBs += cchild -> (underBs.getOrElse(cchild, Set()) + b)
            cParent += cchild -> cparent
          }
        }

        def bParents(b: Identifier): Set[Identifier] = {
          val parentBs = underBs.getOrElse(cOfB(b), Set())

          Set(b) ++ parentBs.flatMap(bParents)
        }

        // include parents
        val keptBs = initialBs.flatMap(bParents)

        //println("Initial Bs: "+initialBs)
        //println("Keeping Bs: "+keptBs)

        //debugCExpr(cTree, keptBs)

        var newCTree = Map[Identifier, Seq[(Identifier, Expr, Set[Identifier])]]()

        for ((c, alts) <- cTree) yield {
          newCTree += c -> alts.filter(a => keptBs(a._1))
        }

        def removeDeadAlts(c: Identifier, deadC: Identifier) {
          if (newCTree contains c) {
            val alts = newCTree(c)
            val newAlts = alts.filterNot(a => a._3 contains deadC)

            if (newAlts.isEmpty) {
              for (cp <- cParent.get(c)) {
                removeDeadAlts(cp, c)
              }
              newCTree -= c
            } else {
              newCTree += c -> newAlts
            }
          }
        }

        //println("BETWEEN")
        //debugCExpr(newCTree, keptBs)

        for ((c, alts) <- newCTree if alts.isEmpty) {
          for (cp <- cParent.get(c)) {
            removeDeadAlts(cp, c)
          }
          newCTree -= c
        }

        var newCDeps = Map[Identifier, Set[Identifier]]()

        for ((c, alts) <- cTree) yield {
          newCDeps += c -> alts.map(_._3).toSet.flatten
        }

        cTree        = newCTree
        cDeps        = newCDeps
        closedBs     = closedBs.filterKeys(keptBs)

        bs           = cTree.map(_._2.map(_._1)).flatten.toSet
        bsOrdered    = bs.toSeq.sortBy(_.id)

        excludedPrograms = excludedPrograms.filter(_.forall(bs))

        //debugCExpr(cTree)
        updateCTree()
      }

      class CGenerator {
        private var buffers = Map[T, Stream[Identifier]]()
        
        private var slots = Map[T, Int]().withDefaultValue(0)

        private def streamOf(t: T): Stream[Identifier] = {
          FreshIdentifier("c", t.getType, true) #:: streamOf(t)
        }

        def reset(): Unit = {
          slots = Map[T, Int]().withDefaultValue(0)
        }

        def getNext(t: T) = {
          if (!(buffers contains t)) {
            buffers += t -> streamOf(t)
          }

          val n = slots(t)
          slots += t -> (n+1)

          buffers(t)(n)
        }
      }

      def unfold(finalUnfolding: Boolean): Boolean = {
        var newBs = Set[Identifier]()
        var unfoldedSomething = false

        def freshB() = {
          val id = FreshIdentifier("B", BooleanType, true)
          newBs += id
          id
        }

        val unfoldBehind = if (cTree.isEmpty) {
          p.xs
        } else {
          closedBs.flatMap(_._2).toSet
        }

        closedBs = Map[Identifier, Set[Identifier]]()

        for (c <- unfoldBehind) {
          var alts = grammar.getProductions(labels(c))

          if (finalUnfolding) {
            alts = alts.filter(_.subTrees.isEmpty)
          }

          val cGen = new CGenerator()

          val cTreeInfos = if (alts.nonEmpty) {
            for (gen <- alts) yield {
              val b = freshB()

              // Optimize labels
              cGen.reset()

              val cToLabel = for (t <- gen.subTrees) yield {
                cGen.getNext(t) -> t
              }


              labels ++= cToLabel

              val cs = cToLabel.map(_._1)
              val ex = gen.builder(cs.map(_.toVariable))

              if (cs.nonEmpty) {
                closedBs += b -> cs.toSet
              }

              //println(" + "+b+" => "+c+" = "+ex)

              unfoldedSomething = true

              (b, ex, cs.toSet)
            }
          } else {
            // Happens in final unfolding when no alts have ground terms
            val b = freshB()
            closedBs += b -> Set()

            Seq((b, simplestValue(c.getType), Set[Identifier]()))
          }

          cTree += c -> cTreeInfos
          cDeps += c -> cTreeInfos.map(_._3).toSet.flatten
        }

        sctx.reporter.ifDebug { printer =>
          printer("Grammar so far:")
          grammar.printProductions(printer)
        }

        bs           = bs ++ newBs
        bsOrdered    = bs.toSeq.sortBy(_.id)

        /**
         * Close dead-ends
         *
         * Find 'c' that have no active alternatives, then close all 'b's that
         * depend on such "dead" 'c's
         */
        var deadCs = Set[Identifier]()

        for ((c, alts) <- cTree) {
          if (alts.forall{ case (b, _, _) => !isBActive(b) }) {
            deadCs += c
          }
        }

        for ((_, alts) <- cTree; (b, _, cs) <- alts) {
          if ((cs & deadCs).nonEmpty) {
            closedBs += (b -> closedBs.getOrElse(b, Set()))
          }
        }

        //debugCExpr(cTree)
        updateCTree()

        unfoldedSomething
      }

      def solveForTentativeProgram(): Option[Option[Set[Identifier]]] = {
        val solverf = SolverFactory.default(ctx, programCTree).withTimeout(exSolverTo)
        val solver  = solverf.getNewSolver()
        val cnstr = FunctionInvocation(phiFd.typed, phiFd.params.map(_.id.toVariable))
        //debugCExpr(cTree)

        //println(" --- PhiFD ---")
        //println(phiFd.fullBody.asString(ctx))

        val fixedBs = finiteArray(bsOrdered.map(_.toVariable), None, BooleanType)
        val cnstrFixed = replaceFromIDs(Map(bArrayId -> fixedBs), cnstr)

        try {
          val toFind = and(p.pc, cnstrFixed)
          //println(" --- Constraints ---")
          //println(" - "+toFind)
          solver.assertCnstr(toFind)

          // oneOfBs
          //println(" -- OneOf:")
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

      def solveForCounterExample(bs: Set[Identifier]): Option[Option[Seq[Expr]]] = {
        val solverf = SolverFactory.default(ctx, programCTree).withTimeout(cexSolverTo)
        val solver  = solverf.getNewSolver()
        val cnstr = FunctionInvocation(phiFd.typed, phiFd.params.map(_.id.toVariable))

        val fixedBs = finiteArray(bsOrdered.map(b => BooleanLiteral(bs(b))), None, BooleanType)
        val cnstrFixed = replaceFromIDs(Map(bArrayId -> fixedBs), cnstr)

        try {
          solver.assertCnstr(p.pc)
          solver.assertCnstr(Not(cnstrFixed))

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
        var unfolding = 1
        val maxUnfoldings = params.maxUnfoldings

        sctx.reporter.debug(s"maxUnfoldings=$maxUnfoldings")

        var baseExampleInputs: ArrayBuffer[Seq[Expr]] = new ArrayBuffer[Seq[Expr]]()

        // We populate the list of examples with a predefined one
        sctx.reporter.debug("Acquiring initial list of examples")

        val ef = new ExamplesFinder(sctx.context, sctx.program)
        baseExampleInputs ++= ef.extractTests(p).map(_.ins).toSet

        val pc = p.pc

        if (pc == BooleanLiteral(true)) {
          baseExampleInputs += p.as.map(a => simplestValue(a.getType))
        } else {
          val solver = sctx.newSolver.setTimeout(exSolverTo)

          solver.assertCnstr(pc)

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
            debug("  - "+in.mkString(", "))
          }
        }

        /**
         * We generate tests for discarding potential programs
         */
        val inputIterator: Iterator[Seq[Expr]] = if (useVanuatoo) {
          new VanuatooDataGen(sctx.context, sctx.program).generateFor(p.as, pc, 20, 3000)
        } else {
          val evaluator  = new DualEvaluator(sctx.context, sctx.program, CodeGenParams.default)
          new GrammarDataGen(evaluator, ExpressionGrammars.ValueGrammar).generateFor(p.as, pc, 20, 1000)
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
                    sctx.reporter.debug(f" Program: ${ndProgram.getExpr(bs)}%-80s failed on: ${e.mkString(", ")}")
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
                  ndProgram.shrinkTo(bssToKeep, unfolding == maxUnfoldings)
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
