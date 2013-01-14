package leon
package synthesis
package rules

import solvers.TimeoutSolver
import purescala.Trees._
import purescala.Common._
import purescala.Definitions._
import purescala.TypeTrees._
import purescala.TreeOps._
import purescala.Extractors._
import purescala.ScalaPrinter

import evaluators._

import solvers.z3.FairZ3Solver

case object CEGIS extends Rule("CEGIS") {
  def instantiateOn(sctx: SynthesisContext, p: Problem): Traversable[RuleInstantiation] = {

    // CEGIS Flags to actiave or de-activate features
    val useCEAsserts          = false
    val useUninterpretedProbe = false
    val useUnsatCores         = true
    val useFunGenerators      = sctx.options.cegisGenerateFunCalls
    val useBPaths             = sctx.options.cegisUseBPaths
    val useCETests            = sctx.options.cegisUseCETests
    val useCEPruning          = sctx.options.cegisUseCEPruning
    val evaluator             = new CodeGenEvaluator(sctx.context, sctx.program)

    case class Generator(tpe: TypeTree, altBuilder: () => List[(Expr, Set[Identifier])]);

    var generators = Map[TypeTree, Generator]()
    def getGenerator(t: TypeTree): Generator = generators.get(t) match {
      case Some(g) => g
      case None =>
        val alternatives: () => List[(Expr, Set[Identifier])] = t match {
          case BooleanType =>
            { () => List((BooleanLiteral(true), Set()), (BooleanLiteral(false), Set())) }

          case Int32Type =>
            { () => List((IntLiteral(0), Set()), (IntLiteral(1), Set())) }

          case TupleType(tps) =>
            { () =>
              val ids = tps.map(t => FreshIdentifier("t", true).setType(t))
              List((Tuple(ids.map(Variable(_))), ids.toSet))
            }

          case CaseClassType(cd) =>
            { () =>
              val ids = cd.fieldsIds.map(i => FreshIdentifier("c", true).setType(i.getType))
              List((CaseClass(cd, ids.map(Variable(_))), ids.toSet))
            }

          case AbstractClassType(cd) =>
            { () =>
              val alts: Seq[(Expr, Set[Identifier])] = cd.knownDescendents.flatMap(i => i match {
                  case acd: AbstractClassDef =>
                    sctx.reporter.error("Unnexpected abstract class in descendants!")
                    None
                  case cd: CaseClassDef =>
                    val ids = cd.fieldsIds.map(i => FreshIdentifier("c", true).setType(i.getType))
                    Some((CaseClass(cd, ids.map(Variable(_))), ids.toSet))
              })
              alts.toList
            }

          case _ =>
            sctx.reporter.error("Can't construct generator. Unsupported type: "+t+"["+t.getClass+"]");
            { () => Nil }
        }
        val g = Generator(t, alternatives)
        generators += t -> g
        g
    }

    def inputAlternatives(t: TypeTree): List[(Expr, Set[Identifier])] = {
      p.as.filter(a => isSubtypeOf(a.getType, t)).map(id => (Variable(id) : Expr, Set[Identifier]()))
    }

    def funcAlternatives(t: TypeTree): List[(Expr, Set[Identifier])] = {
      if (useFunGenerators) {
        def isCandidate(fd: FunDef): Boolean = {
          // Prevents recursive calls
          val isRecursiveCall = sctx.functionContext match {
            case Some(cfd) =>
              (sctx.program.transitiveCallers(cfd) + cfd) contains fd

            case None =>
              false
          }

          val isNotSynthesizable = fd.body match {
            case Some(b) =>
              collectChooses(b).isEmpty

            case None =>
              false
          }



          isSubtypeOf(fd.returnType, t) && !isRecursiveCall && isNotSynthesizable
        }

        sctx.program.definedFunctions.filter(isCandidate).map{ fd =>
          val ids = fd.args.map(vd => FreshIdentifier("c", true).setType(vd.getType))

          (FunctionInvocation(fd, ids.map(Variable(_))), ids.toSet)
        }.toList
      } else {
        Nil
      }
    }

    class NonDeterministicProgram(val p: Problem,
                                  val initGuard: Identifier) {

      //var program: Expr = BooleanLiteral(true)

      // b -> (c, ex) means the clause b => c == ex
      var mappings: Map[Identifier, (Identifier, Expr)] = Map()

      // b -> Set(c1, c2) means c1 and c2 are uninterpreted behing b, requires b to be closed
      private var guardedTerms: Map[Identifier, Set[Identifier]] = Map(initGuard -> p.xs.toSet)


      def isBClosed(b: Identifier) = guardedTerms.contains(b)

      // b -> Map(c1 -> Set(b2, b3), c2 -> Set(b4, b5)) means b protects c1 (with sub alternatives b2/b3), and c2 (with sub b4/b5)
      private var bTree = Map[Identifier, Map[Identifier, Set[Identifier]]]( initGuard -> p.xs.map(_ -> Set[Identifier]()).toMap)

      // Returns all possible assignments to Bs in order to enumerate all possible programs
      def allPrograms(): Set[Set[Identifier]] = {
        def allChildPaths(b: Identifier): Stream[Set[Identifier]] = {
          if (isBClosed(b)) {
            Stream.empty
          } else {
            bTree.get(b) match {
              case Some(cToBs) =>
                val streams = cToBs.values.map { children =>
                  children.toStream.flatMap(c => allChildPaths(c).map(l => l + b))
                }

                streams.reduceLeft{ (s1: Stream[Set[Identifier]], s2: Stream[Set[Identifier]]) => for(p1 <- s1; p2 <- s2) yield { p1 ++ p2 } }
              case None =>
                Stream.cons(Set(b), Stream.empty)
            }
          }
        }

        allChildPaths(initGuard).toSet
      }

      /*
       * Compilation/Execution of programs
       */

      // b1 => c == F(c2, c3) OR b2 => c == F(c4, c5) is represented here as c -> Set(c2, c3, c4, c5)
      private var cChildren: Map[Identifier, Set[Identifier]] = Map().withDefaultValue(Set())


      private var triedCompilation = false
      private var progEvaluator: Option[(Seq[Expr], Seq[Expr]) => EvaluationResult] = None

      def canTest() = {
        if (!triedCompilation) {
          progEvaluator = compile()
        }

        progEvaluator.isDefined
      }

      private var bssOrdered: Seq[Identifier] = Seq()

      def testForProgram(bss: Set[Identifier])(ins: Seq[Expr]): Boolean = {
        if (canTest()) {
          val bssValues : Seq[Expr] = bssOrdered.map(i => BooleanLiteral(bss(i)))

          val evalResult = progEvaluator.get.apply(bssValues,  ins)

          evalResult match {
            case EvaluationSuccessful(res) =>
              res == BooleanLiteral(true)

            case EvaluationError(err) =>
              sctx.reporter.error("Error testing CE: "+err)
              true

            case EvaluationFailure(err) =>
              sctx.reporter.error("Error testing CE: "+err)
              true
          }
        } else {
          true
        }
      }

      def compile(): Option[(Seq[Expr], Seq[Expr]) => EvaluationResult] = {
        var unreachableCs: Set[Identifier] = guardedTerms.flatMap(_._2).toSet

        val cToExprs = mappings.groupBy(_._2._1).map {
          case (c, maps) =>
            // We only keep cases within the current unrolling closedBs
            val cases = maps.flatMap{ case (b, (_, ex)) => if (isBClosed(b)) None else Some(b -> ex) }

            // We compute the IF expression corresponding to each c
            val ifExpr = if (cases.isEmpty) {
              // This can happen with ADTs with only cases with arguments
              Error("No valid clause available").setType(c.getType)
            } else {
              cases.tail.foldLeft(cases.head._2) {
                case (elze, (b, then)) => IfExpr(Variable(b), then, elze)
              }
            }

            c -> ifExpr
        } toMap

        // Map each x generated by the program to fresh xs passed as argument
        val newXs = p.xs.map(x => x -> FreshIdentifier(x.name, true).setType(x.getType))

        val baseExpr = p.phi

        bssOrdered = bss.toSeq.sortBy(_.id)

        var res = baseExpr

        def composeWith(c: Identifier) {
          cToExprs.get(c) match {
            case Some(value) =>
              res = Let(c, cToExprs(c), res)
            case None =>
              res = Let(c, Error("No value available").setType(c.getType), res)
          }

          for (dep <- cChildren(c) if !unreachableCs(dep)) {
            composeWith(dep)
          }

        }

        for (c <- p.xs) {
          composeWith(c)
        }

        val simplerRes = simplifyLets(res)

        // println("COMPILATION RESULT: ")
        // println(ScalaPrinter(simplerRes))
        // println("BSS: "+bssOrdered)
        // println("FREE: "+variablesOf(simplerRes))

        def compileWithArray(): Option[(Seq[Expr], Seq[Expr]) => EvaluationResult] = {
          val ba = FreshIdentifier("bssArray").setType(ArrayType(BooleanType))
          val bav = Variable(ba)
          val substMap : Map[Expr,Expr] = (bssOrdered.zipWithIndex.map {
            case (b,i) => Variable(b) -> ArraySelect(bav, IntLiteral(i)).setType(BooleanType)
          }).toMap
          val forArray = replace(substMap, simplerRes)

          // println("FORARRAY RESULT: ")
          // println(ScalaPrinter(forArray))
          // println("FREE: "+variablesOf(simplerRes))

          // We trust arrays to be fast...
          // val simple = evaluator.compile(simplerRes, bssOrdered ++ p.as)
          val eval = evaluator.compile(forArray, ba +: p.as)

          eval.map{e => { case (bss, ins) => 
            e(FiniteArray(bss).setType(ArrayType(BooleanType)) +: ins)
          }}
        }

        def compileWithArgs(): Option[(Seq[Expr], Seq[Expr]) => EvaluationResult] = {
          val eval = evaluator.compile(simplerRes, bssOrdered ++ p.as)

          eval.map{e => { case (bss, ins) => 
            e(bss ++ ins)
          }}
        }

        triedCompilation = true

        val localVariables = bss.size + cToExprs.size + p.as.size

        if (localVariables < 128) {
          compileWithArgs().orElse(compileWithArray())
        } else {
          compileWithArray()
        }
      }

      def determinize(bss: Set[Identifier]): Expr = {
        val cClauses = mappings.filterKeys(bss).map(_._2).toMap

        def getCValue(c: Identifier): Expr = {
          val map = for (dep <- cChildren(c) if cClauses contains dep) yield {
            dep -> getCValue(dep)
          }

          substAll(map.toMap, cClauses(c))
        }

        Tuple(p.xs.map(c => getCValue(c))).setType(TupleType(p.xs.map(_.getType)))

      }

      def unroll: (List[Expr], Set[Identifier]) = {
        var newClauses      = List[Expr]()
        var newGuardedTerms = Map[Identifier, Set[Identifier]]()
        var newMappings     = Map[Identifier, (Identifier, Expr)]()

        for ((parentGuard, recIds) <- guardedTerms; recId <- recIds) {

          val gen  = getGenerator(recId.getType)

          val alts = gen.altBuilder() ::: inputAlternatives(recId.getType) ::: funcAlternatives(recId.getType)

          val altsWithBranches = alts.map(alt => FreshIdentifier("B", true).setType(BooleanType) -> alt)

          val bvs  = altsWithBranches.map(alt => Variable(alt._1))

          val failedPath = Not(Variable(parentGuard))

          val distinct = bvs.combinations(2).collect {
            case List(a, b) =>
              Or(Not(a) :: Not(b) :: Nil)
          }

          val pre = And(Seq(Or(failedPath :: bvs), Implies(failedPath, And(bvs.map(Not(_))))) ++ distinct)

          val cases = for((bid, (ex, rec)) <- altsWithBranches.toList) yield { // b1 => E(gen1, gen2)     [b1 -> {gen1, gen2}]
            if (!rec.isEmpty) {
              newGuardedTerms += bid -> rec
              cChildren       += recId -> (cChildren(recId) ++ rec)
            }

            newMappings  += bid -> (recId -> ex)

            Implies(Variable(bid), Equals(Variable(recId), ex))
          }

          val newBIds = altsWithBranches.map(_._1).toSet
          bTree += parentGuard -> (bTree.getOrElse(parentGuard, Map()) + (recId -> newBIds))

          newClauses = newClauses ::: pre :: cases
        }

        //program  = And(program :: newClauses)

        mappings = mappings ++ newMappings

        guardedTerms = newGuardedTerms

        // Finally, we reset the state of the evalautor
        triedCompilation = false
        progEvaluator    = None

        (newClauses, newGuardedTerms.keySet)
      }

      def bss = mappings.keySet
      def css : Set[Identifier] = mappings.values.map(_._1).toSet ++ guardedTerms.flatMap(_._2)
    }

    val TopLevelAnds(ands) = p.phi

    val xsSet = p.xs.toSet


    val (exprsA, others) = ands.partition(e => (variablesOf(e) & xsSet).isEmpty)
    if (exprsA.isEmpty) {
      val res = new RuleInstantiation(p, this, SolutionBuilder.none) {
        def apply(sctx: SynthesisContext): RuleApplicationResult = {
          var result: Option[RuleApplicationResult]   = None

          var ass = p.as.toSet
          var xss = p.xs.toSet

          val initGuard = FreshIdentifier("START", true).setType(BooleanType)

          val ndProgram = new NonDeterministicProgram(p, initGuard)
          var unrolings = 0
          val maxUnrolings = 3

          val mainSolver = new TimeoutSolver(sctx.solver, 2000L) // 2sec

          var exampleInputs = Set[Seq[Expr]]()

          // We populate the list of examples with a predefined one
          if (p.pc == BooleanLiteral(true)) {
            exampleInputs += p.as.map(a => simplestValue(a.getType))
          } else {
            val solver = mainSolver.getNewSolver

            solver.assertCnstr(p.pc)

            solver.check match {
              case Some(true) =>
                val model = solver.getModel
                exampleInputs += p.as.map(a => model.getOrElse(a, simplestValue(a.getType)))

              case Some(false) =>
                return RuleApplicationImpossible

              case None =>
                sctx.reporter.warning("Solver could not solve path-condition")
                return RuleApplicationImpossible // This is not necessary though, but probably wanted
            }
          }

          // Keep track of collected cores to filter programs to test
          var collectedCores = Set[Set[Identifier]]()

          // solver1 is used for the initial SAT queries
          var solver1 = mainSolver.getNewSolver
          solver1.assertCnstr(And(p.pc :: p.phi :: Variable(initGuard) :: Nil))

          // solver2 is used for validating a candidate program, or finding new inputs
          val solver2 = mainSolver.getNewSolver
          solver2.assertCnstr(And(p.pc :: Not(p.phi) :: Variable(initGuard) :: Nil))


          var allClauses = List[Expr]()

          try {
            do {
              var needMoreUnrolling = false

              // Compute all programs that have not been excluded yet
              var allPrograms: Set[Set[Identifier]] = if (useCEPruning) {
                ndProgram.allPrograms.filterNot(p => collectedCores.exists(c => c.subsetOf(p)))
              } else {
                Set()
              }

              //println("Programs: "+allPrograms.size)
              //println("CEs:      "+exampleInputs.size)

              // We further filter the set of working programs to remove those that fail on known examples
              if (useCEPruning && !exampleInputs.isEmpty && ndProgram.canTest()) {
                //for (ce <- exampleInputs) {
                //  println("CE: "+ce)
                //}

                for (p <- allPrograms) {
                  if (!exampleInputs.forall(ndProgram.testForProgram(p))) {
                    // This program failed on at least one example
                    solver1.assertCnstr(Not(And(p.map(Variable(_)).toSeq)))
                    allPrograms -= p
                  }
                }

                if (allPrograms.isEmpty) {
                  needMoreUnrolling = true
                }

                //println("Passing tests: "+allPrograms.size)
              }

              //allPrograms.foreach { p =>
              //  println("PATH: "+p)
              //  println("CLAUSES: "+p.flatMap( b => ndProgram.mappings.get(b).map{ case (c, ex) => c+" = "+ex}).mkString(" && "))
              //}

              val (clauses, closedBs) = ndProgram.unroll
              //println("UNROLLING: ")
              //for (c <- clauses) {
              //  println(" - " + c)
              //}
              //println("CLOSED Bs "+closedBs)

              val clause = And(clauses)
              allClauses = clause :: allClauses

              solver1.assertCnstr(clause)
              solver2.assertCnstr(clause)

              val tpe = TupleType(p.xs.map(_.getType))
              val bss = ndProgram.bss

              if (clauses.isEmpty) {
                needMoreUnrolling = true
              }

              while (result.isEmpty && !needMoreUnrolling && !sctx.shouldStop.get) {

                solver1.checkAssumptions(closedBs.map(id => Not(Variable(id)))) match {
                  case Some(true) =>
                    val satModel = solver1.getModel

                    val bssAssumptions: Set[Expr] = bss.map(b => satModel(b) match {
                      case BooleanLiteral(true)  => Variable(b)
                      case BooleanLiteral(false) => Not(Variable(b))
                    })

                    //println("CEGIS OUT!")
                    //println("Found solution: "+bssAssumptions)

                    //bssAssumptions.collect { case Variable(b) => ndProgram.mappings(b) }.foreach {
                    //  case (c, ex) =>
                    //    println(". "+c+" = "+ex)
                    //}

                    val validateWithZ3 = if (useCETests && !exampleInputs.isEmpty && ndProgram.canTest()) {

                      val p = bssAssumptions.collect { case Variable(b) => b }

                      if (exampleInputs.forall(ndProgram.testForProgram(p))) {
                        // All valid inputs also work with this, we need to
                        // make sure by validating this candidate with z3
                        true
                      } else {
                        // One valid input failed with this candidate, we can skip
                        solver1.assertCnstr(Not(And(p.map(Variable(_)).toSeq)))
                        false
                      }
                    } else {
                      // No inputs or capability to test, we need to ask Z3
                      true
                    }

                    if (validateWithZ3) {
                      solver2.checkAssumptions(bssAssumptions) match {
                        case Some(true) =>
                          //println("#"*80)
                          val invalidModel = solver2.getModel

                          val fixedAss = And(ass.collect {
                            case a if invalidModel contains a => Equals(Variable(a), invalidModel(a))
                          }.toSeq)

                          val newCE = p.as.map(valuateWithModel(invalidModel))

                          exampleInputs += newCE

                          //println("Found counter example: "+fixedAss)

                          // Retest whether the newly found C-E invalidates all programs
                          if (useCEPruning && ndProgram.canTest) {
                            if (allPrograms.forall(p => !ndProgram.testForProgram(p)(newCE))) {
                              // println("I found a killer example!")
                              needMoreUnrolling = true
                            }
                          }

                          val unsatCore = if (useUnsatCores) {
                            solver1.push()
                            solver1.assertCnstr(fixedAss)

                            val core = solver1.checkAssumptions(bssAssumptions) match {
                              case Some(false) =>
                                // Core might be empty if unrolling level is
                                // insufficient, it becomes unsat no matter what
                                // the assumptions are.
                                solver1.getUnsatCore

                              case _ =>
                                bssAssumptions
                            }

                            solver1.pop()

                            collectedCores += core.collect{ case Variable(id) => id }

                            core
                          } else {
                            bssAssumptions
                          }

                          if (unsatCore.isEmpty) {
                            needMoreUnrolling = true
                          } else {
                            //if (useCEAsserts) {
                            //  val freshCss = ndProgram.css.map(c => c -> Variable(FreshIdentifier(c.name, true).setType(c.getType))).toMap
                            //  val ceIn     = ass.collect { 
                            //    case id if invalidModel contains id => id -> invalidModel(id)
                            //  }

                            //  val ceMap = (freshCss ++ ceIn)

                            //  val counterexample = substAll(ceMap, And(Seq(ndProgram.program, p.phi)))

                            //  //val And(ands) = counterexample
                            //  //println("CE:")
                            //  //for (a <- ands) {
                            //  //  println(" - "+a)
                            //  //}

                            //  solver1.assertCnstr(counterexample)
                            //}

                            solver1.assertCnstr(Not(And(unsatCore.toSeq)))
                          }

                        case Some(false) =>

                          val expr = ndProgram.determinize(satModel.filter(_._2 == BooleanLiteral(true)).keySet)

                          result = Some(RuleSuccess(Solution(BooleanLiteral(true), Set(), expr)))

                        case _ =>
                          if (!sctx.shouldStop.get) {
                            sctx.reporter.warning("Solver returned 'UNKNOWN' in a CEGIS iteration.")
                          }
                          needMoreUnrolling = true
                      }
                    }


                  case Some(false) =>
                    //println("%%%% UNSAT")

                    if (useUninterpretedProbe) {
                      solver1.check match {
                        case Some(false) =>
                          // Unsat even without blockers (under which fcalls are then uninterpreted)
                          result = Some(RuleApplicationImpossible)

                        case _ =>
                      }
                    }

                    needMoreUnrolling = true

                  case _ =>
                    if (!sctx.shouldStop.get) {
                      sctx.reporter.warning("Solver returned 'UNKNOWN' in a CEGIS iteration.")
                    }
                    //println("%%%% WOOPS")
                    needMoreUnrolling = true
                }
              }

              unrolings += 1
            } while(unrolings < maxUnrolings && result.isEmpty && !sctx.shouldStop.get)

            result.getOrElse(RuleApplicationImpossible)

          } catch {
            case e: Throwable =>
              sctx.reporter.warning("CEGIS crashed: "+e.getMessage)
              e.printStackTrace
              RuleApplicationImpossible
          }
        }
      }
      List(res)
    } else {
      Nil
    }
  }
}
