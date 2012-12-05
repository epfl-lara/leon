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

          newClauses = newClauses ::: pre :: cases
        }

        program  = And(program :: newClauses)
        mappings = mappings ++ newMappings
        recTerms = newRecTerms

        (newClauses, newRecTerms.keySet)
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
              //println("UNROLLING: "+clauses+" WITH BOUNDS "+bounds)
              solver1.assertCnstr(And(clauses))
              solver2.assertCnstr(And(clauses))

              //println("="*80)
              //println("Was: "+lastF.entireFormula)
              //println("Now Trying : "+currentF.entireFormula)

              val tpe = TupleType(p.xs.map(_.getType))
              val bss = unrolling.bss

              var continue = !clauses.isEmpty

              //println("Unrolling #"+unrolings+" bss size: "+bss.size)

              while (result.isEmpty && continue) {
                //println("Looking for CE...")
                //println("-"*80)
                //println(basePhi)

                //println("To satisfy: "+constrainedPhi)
                solver1.checkAssumptions(bounds.map(id => Not(Variable(id)))) match {
                  case Some(true) =>
                    val satModel = solver1.getModel

                    //println("Found solution: "+satModel)
                    //println("Corresponding program: "+simplifyTautologies(synth.solver)(valuateWithModelIn(currentF.program, bss, satModel)))
                    //val fixedBss = And(bss.map(b => Equals(Variable(b), satModel(b))).toSeq)
                    //println("Phi with fixed sat bss: "+fixedBss)

                    val bssAssumptions: Set[Expr] = bss.map(b => satModel(b) match {
                      case BooleanLiteral(true)  => Variable(b)
                      case BooleanLiteral(false) => Not(Variable(b))
                    })

                    //println("FORMULA: "+And(currentF.pathcond :: currentF.program :: Not(currentF.phi) :: fixedBss :: Nil))

                    //println("#"*80)
                    solver2.checkAssumptions(bssAssumptions) match {
                      case Some(true) =>
                        //println("#"*80)
                        val invalidModel = solver2.getModel

                        val fixedAss = And(ass.map(a => Equals(Variable(a), invalidModel(a))).toSeq)

                        solver1.push()
                        solver1.assertCnstr(fixedAss)
                        //println("Found counter example: "+fixedAss)

                        val unsatCore = solver1.checkAssumptions(bssAssumptions) match {
                          case Some(false) =>
                            val core = solver1.getUnsatCore
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

                        solver1.pop()

                        if (unsatCore.isEmpty) {
                          continue = false
                        } else {

                          val freshCss = unrolling.css.map(c => c -> Variable(FreshIdentifier(c.name, true).setType(c.getType))).toMap
                          val ceIn     = ass.map(id => id -> invalidModel(id))
                          val counterexemple = substAll(freshCss ++ ceIn, And(Seq(unrolling.program, unrolling.phi)))

                          solver1.assertCnstr(counterexemple)
                          solver2.assertCnstr(counterexemple)

                          //predicates = Not(And(unsatCore.toSeq)) +: counterexemple +: predicates
                          solver1.assertCnstr(Not(And(unsatCore.toSeq)))
                          solver2.assertCnstr(Not(And(unsatCore.toSeq)))
                        }

                      case Some(false) =>
                        //println("#"*80)
                        //println("UNSAT!")
                        //println("Sat model: "+satModel.toSeq.sortBy(_._1.toString).map{ case (id, v) => id+" -> "+v }.mkString(", "))
                        var mapping = unrolling.mappings.filterKeys(satModel.mapValues(_ == BooleanLiteral(true))).values.toMap


                        // Resolve mapping
                        for ((c, e) <- mapping) {
                          mapping += c -> substAll(mapping, e)
                        }

                        result = Some(RuleSuccess(Solution(BooleanLiteral(true), Set(), Tuple(p.xs.map(valuateWithModel(mapping))).setType(tpe))))

                      case _ =>
                        sctx.reporter.warning("Solver returned 'UNKNOWN' in a CEGIS iteration.")
                        continue = false
                    }

                  case Some(false) =>
                    //println("%%%% UNSAT")
                    continue = false
                  case _ =>
                    //println("%%%% WOOPS")
                    continue = false
                }
              }

              unrolings += 1
            } while(unrolings < maxUnrolings && result.isEmpty)

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
