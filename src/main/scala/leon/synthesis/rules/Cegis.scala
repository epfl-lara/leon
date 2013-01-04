package leon
package synthesis
package rules

import purescala.Trees._
import purescala.Common._
import purescala.Definitions._
import purescala.TypeTrees._
import purescala.TreeOps._
import purescala.Extractors._

import solvers.z3.FairZ3Solver

case object CEGIS extends Rule("CEGIS") {
  def instantiateOn(sctx: SynthesisContext, p: Problem): Traversable[RuleInstantiation] = {

    // CEGIS Flags to actiave or de-activate features
    val useCounterExamples    = false
    val useUninterpretedProbe = false
    val useUnsatCores         = true
    val useFunGenerators      = sctx.options.cegisGenerateFunCalls

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

          isSubtypeOf(fd.returnType, t) && !isRecursiveCall
        }

        sctx.program.definedFunctions.filter(isCandidate).map{ fd =>
          val ids = fd.args.map(vd => FreshIdentifier("c", true).setType(vd.getType))

          (FunctionInvocation(fd, ids.map(Variable(_))), ids.toSet)
        }.toList
      } else {
        Nil
      }
    }

    class TentativeFormula(val pathcond: Expr,
                           val phi: Expr,
                           var program: Expr,
                           var mappings: Map[Identifier, (Identifier, Expr)],
                           var recTerms: Map[Identifier, Set[Identifier]]) {

      def unroll: (List[Expr], Set[Identifier]) = {
        var newClauses  = List[Expr]()
        var newRecTerms = Map[Identifier, Set[Identifier]]()
        var newMappings = Map[Identifier, (Identifier, Expr)]()

        for ((_, recIds) <- recTerms; recId <- recIds) {
          val gen  = getGenerator(recId.getType)
          val alts = gen.altBuilder() ::: inputAlternatives(recId.getType) ::: funcAlternatives(recId.getType)

          val altsWithBranches = alts.map(alt => FreshIdentifier("b", true).setType(BooleanType) -> alt)

          val bvs = altsWithBranches.map(alt => Variable(alt._1))
          val distinct = if (bvs.size > 1) {
            (for (i <- (1 to bvs.size-1); j <- 0 to i-1) yield {
              Or(Not(bvs(i)), Not(bvs(j)))
            }).toList
          } else {
            List(BooleanLiteral(true))
          }
          val pre = And(Or(bvs) :: distinct) // (b1 OR b2) AND (Not(b1) OR Not(b2))
          val cases = for((bid, (ex, rec)) <- altsWithBranches.toList) yield { // b1 => E(gen1, gen2)     [b1 -> {gen1, gen2}]
            if (!rec.isEmpty) {
              newRecTerms += bid -> rec
            }
            newMappings += bid -> (recId -> ex)

            Implies(Variable(bid), Equals(Variable(recId), ex))
          }

          newClauses = newClauses ::: pre :: cases
        }

        program  = And(program :: newClauses)

        mappings = mappings ++ newMappings

        recTerms = newRecTerms

        (newClauses, newRecTerms.keySet)
      }

      def bounds = recTerms.keySet.map(id => Not(Variable(id))).toList
      def bss = mappings.keySet
      def css : Set[Identifier] = mappings.values.map(_._1).toSet ++ recTerms.flatMap(_._2)

      def entireFormula = And(pathcond :: phi :: program :: bounds)
    }

    val TopLevelAnds(ands) = p.phi

    val xsSet = p.xs.toSet


    val (exprsA, others) = ands.partition(e => (variablesOf(e) & xsSet).isEmpty)
    if (exprsA.isEmpty) {
      val res = new RuleInstantiation(p, this, SolutionBuilder.none) {
        def apply(sctx: SynthesisContext) = {
          var result: Option[RuleApplicationResult]   = None

          var ass = p.as.toSet
          var xss = p.xs.toSet

          val unrolling = new TentativeFormula(p.pc, p.phi, BooleanLiteral(true), Map(), Map() ++ p.xs.map(x => x -> Set(x)))
          var unrolings = 0
          val maxUnrolings = 3
          var predicates: Seq[Expr]        = Seq()


          val mainSolver: FairZ3Solver = sctx.solver.asInstanceOf[FairZ3Solver]

          // solver1 is used for the initial SAT queries
          val solver1 = mainSolver.getNewSolver
          solver1.assertCnstr(And(p.pc, p.phi))

          // solver2 is used for the CE search
          val solver2 = mainSolver.getNewSolver
          solver2.assertCnstr(And(p.pc :: Not(p.phi) :: Nil))

          try {
            do {
              val (clauses, bounds) = unrolling.unroll
              //println("UNROLLING: ")
              //for (c <- clauses) {
              //  println(" - " + c)
              //}
              //println("BOUNDS "+bounds)

              val clause = And(clauses)
              solver1.assertCnstr(clause)
              solver2.assertCnstr(clause)

              val tpe = TupleType(p.xs.map(_.getType))
              val bss = unrolling.bss

              var continue = !clauses.isEmpty

              while (result.isEmpty && continue && !sctx.shouldStop.get) {
                //println("Looking for CE...")
                //println("-"*80)

                solver1.checkAssumptions(bounds.map(id => Not(Variable(id)))) match {
                  case Some(true) =>
                    val satModel = solver1.getModel

                    val bssAssumptions: Set[Expr] = bss.map(b => satModel(b) match {
                      case BooleanLiteral(true)  => Variable(b)
                      case BooleanLiteral(false) => Not(Variable(b))
                    })

                    //println("Found solution: "+bssAssumptions)

                    //println("#"*80)
                    solver2.checkAssumptions(bssAssumptions) match {
                      case Some(true) =>
                        //println("#"*80)
                        val invalidModel = solver2.getModel

                        val fixedAss = And(ass.collect {
                          case a if invalidModel contains a => Equals(Variable(a), invalidModel(a))
                        }.toSeq)

                        solver1.push()
                        solver1.assertCnstr(fixedAss)
                        //println("Found counter example: "+fixedAss)

                        val unsatCore = if (useUnsatCores) {
                          solver1.checkAssumptions(bssAssumptions) match {
                            case Some(false) =>
                              // Core might be empty if unrolling level is
                              // insufficient, it becomes unsat no matter what
                              // the assumptions are.
                              solver1.getUnsatCore
                            case _ =>
                              bssAssumptions
                          }
                        } else {
                          bssAssumptions
                        }

                        solver1.pop()

                        if (unsatCore.isEmpty) {
                          continue = false
                        } else {
                          if (useCounterExamples) {
                            val freshCss = unrolling.css.map(c => c -> Variable(FreshIdentifier(c.name, true).setType(c.getType))).toMap
                            val ceIn     = ass.collect { 
                              case id if invalidModel contains id => id -> invalidModel(id)
                            }

                            val ceMap = (freshCss ++ ceIn)

                            val counterexample = substAll(ceMap, And(Seq(unrolling.program, unrolling.phi)))

                            //val And(ands) = counterexample
                            //println("CE:")
                            //for (a <- ands) {
                            //  println(" - "+a)
                            //}

                            solver1.assertCnstr(counterexample)
                          }

                          solver1.assertCnstr(Not(And(unsatCore.toSeq)))
                        }

                      case Some(false) =>
                        var mapping = unrolling.mappings.filterKeys(satModel.mapValues(_ == BooleanLiteral(true))).values.toMap

                        // Resolve mapping
                        for ((c, e) <- mapping) {
                          mapping += c -> substAll(mapping, e)
                        }

                        result = Some(RuleSuccess(Solution(BooleanLiteral(true), Set(), Tuple(p.xs.map(valuateWithModel(mapping))).setType(tpe))))

                      case _ =>
                        if (!sctx.shouldStop.get) {
                          sctx.reporter.warning("Solver returned 'UNKNOWN' in a CEGIS iteration.")
                        }
                        continue = false
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

                    continue = false

                  case _ =>
                    //println("%%%% WOOPS")
                    continue = false
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
