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

case object CEGIS extends Rule("CEGIS", 150) {
  def attemptToApplyOn(sctx: SynthesisContext, p: Problem): RuleResult = {
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

    case class TentativeFormula(pathcond: Expr,
                                phi: Expr,
                                program: Expr,
                                mappings: Map[Identifier, (Identifier, Expr)],
                                recTerms: Map[Identifier, Set[Identifier]]) {
      def unroll: TentativeFormula = {
        var newProgram  = List[Expr]()
        var newRecTerms = Map[Identifier, Set[Identifier]]()
        var newMappings = Map[Identifier, (Identifier, Expr)]()

        for ((_, recIds) <- recTerms; recId <- recIds) {
          val gen  = getGenerator(recId.getType)
          val alts = gen.altBuilder() ::: inputAlternatives(recId.getType)

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

          newProgram = newProgram ::: pre :: cases
        }

        TentativeFormula(pathcond, phi, And(program :: newProgram), mappings ++ newMappings, newRecTerms)
      }

      def bounds = recTerms.keySet.map(id => Not(Variable(id))).toList
      def bss = mappings.keySet
      def css = mappings.values.map(_._1)

      def entireFormula = And(pathcond :: phi :: program :: bounds)
    }

    val TopLevelAnds(ands) = p.phi

    val xsSet = p.xs.toSet

    val (exprsA, others) = ands.partition(e => (variablesOf(e) & xsSet).isEmpty)
    if (exprsA.isEmpty) {
      val res = new RuleImmediateApplication {
        def apply() = {
          var result: Option[RuleApplicationResult]   = None

          var ass = p.as.toSet
          var xss = p.xs.toSet

          var lastF     = TentativeFormula(p.pc, p.phi, BooleanLiteral(true), Map(), Map() ++ p.xs.map(x => x -> Set(x)))
          var currentF  = lastF.unroll
          var unrolings = 0
          val maxUnrolings = 3
          var predicates: Seq[Expr]        = Seq()
          try {
            do {
              //println("="*80)
              //println("Was: "+lastF.entireFormula)
              //println("Now Trying : "+currentF.entireFormula)

              val tpe = TupleType(p.xs.map(_.getType))
              val bss = currentF.bss

              var continue = true

              val mainSolver: FairZ3Solver = sctx.solver.asInstanceOf[FairZ3Solver]

              // solver1 is used for the initial SAT queries
              val solver1 = mainSolver.getNewSolver

              val basePhi = currentF.entireFormula
              solver1.assertCnstr(basePhi)

              // solver2 is used for the CE search
              val solver2 = mainSolver.getNewSolver
              solver2.assertCnstr(And(currentF.pathcond :: currentF.program :: Not(currentF.phi) :: Nil))

              // solver3 is used for the unsatcore search
              val solver3 = mainSolver.getNewSolver
              solver3.assertCnstr(And(currentF.pathcond :: currentF.program :: currentF.phi :: Nil))

              while (result.isEmpty && continue) {
                //println("-"*80)
                //println(basePhi)

                //println("To satisfy: "+constrainedPhi)
                solver1.check match {
                  case Some(true) =>
                    val satModel = solver1.getModel

                    //println("Found solution: "+satModel)
                    //println("Corresponding program: "+simplifyTautologies(synth.solver)(valuateWithModelIn(currentF.program, bss, satModel)))
                    val fixedBss = And(bss.map(b => Equals(Variable(b), satModel(b))).toSeq)
                    //println("Phi with fixed sat bss: "+fixedBss)

                    solver2.push()
                    solver2.assertCnstr(fixedBss)

                    //println("FORMULA: "+And(currentF.pathcond :: currentF.program :: Not(currentF.phi) :: fixedBss :: Nil))

                    //println("#"*80)
                    solver2.check match {
                      case Some(true) =>
                        //println("#"*80)
                        val invalidModel = solver2.getModel

                        val fixedAss = And(ass.map(a => Equals(Variable(a), invalidModel(a))).toSeq)

                        //println("Found counter example: "+fixedAss)

                        solver3.push()
                        solver3.assertCnstr(fixedAss)

                        val bssAssumptions: Set[Expr] = bss.toSet.map { b: Identifier => satModel(b) match {
                          case BooleanLiteral(true) => Variable(b)
                          case BooleanLiteral(false) => Not(Variable(b))
                        }}

                        val unsatCore = solver3.checkAssumptions(bssAssumptions) match {
                          case Some(false) =>
                            val core = solver3.getUnsatCore
                            //println("Formula: "+mustBeUnsat)
                            //println("Core:    "+core)
                            //println(synth.solver.solveSAT(And(mustBeUnsat +: bssAssumptions.toSeq)))
                            //println("maxcore: "+bssAssumptions)
                            if (core.isEmpty) {
                              // This happens if unrolling level is insufficient, it becomes unsat no matter what the assumptions are.
                              //sctx.reporter.warning("Got empty core, must be unsat without assumptions!")
                              Set()
                            } else {
                              core
                            }
                          case _ =>
                            bssAssumptions
                        }

                        solver3.pop()

                        val freshCss = currentF.css.map(c => c -> Variable(FreshIdentifier(c.name, true).setType(c.getType))).toMap

                        val ceIn     = ass.map(id => id -> invalidModel(id))

                        val counterexemple = substAll(freshCss ++ ceIn, And(Seq(currentF.program, currentF.phi)))

                        //println("#"*80)
                        //println(currentF.phi)
                        //println(substAll(freshCss ++ ceIn, currentF.phi))

                        // Found as such as the xs break, refine predicates

                        if (unsatCore.isEmpty) {
                          continue = false
                        } else {
                          //predicates = Not(And(unsatCore.toSeq)) +: counterexemple +: predicates
                          solver1.assertCnstr(Not(And(unsatCore.toSeq)))
                        }

                      case Some(false) =>
                        //println("#"*80)
                        //println("UNSAT!")
                        //println("Sat model: "+satModel.toSeq.sortBy(_._1.toString).map{ case (id, v) => id+" -> "+v }.mkString(", "))
                        var mapping = currentF.mappings.filterKeys(satModel.mapValues(_ == BooleanLiteral(true))).values.toMap


                        // Resolve mapping
                        for ((c, e) <- mapping) {
                          mapping += c -> substAll(mapping, e)
                        }

                        result = Some(RuleSuccess(Solution(BooleanLiteral(true), Set(), Tuple(p.xs.map(valuateWithModel(mapping))).setType(tpe))))

                      case _ =>
                        sctx.reporter.warning("Solver returned 'UNKNOWN' in a CEGIS iteration.")
                        continue = false
                    }

                    solver2.pop()

                  case Some(false) =>
                    //println("%%%% UNSAT")
                    continue = false
                  case _ =>
                    //println("%%%% WOOPS")
                    continue = false
                }
              }

              lastF = currentF
              currentF = currentF.unroll
              unrolings += 1
            } while(unrolings < maxUnrolings && lastF != currentF && result.isEmpty)

            result.getOrElse(RuleApplicationImpossible)

          } catch {
            case e: Throwable =>
              sctx.reporter.warning("CEGIS crashed: "+e.getMessage)
              e.printStackTrace
              RuleApplicationImpossible
          }

        }
      }
      RuleResult(List(res))
    } else {
      RuleInapplicable
    }
  }
}
