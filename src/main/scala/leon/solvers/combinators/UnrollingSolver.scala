/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package solvers
package combinators

import purescala.Common._
import purescala.Definitions._
import purescala.Quantification._
import purescala.Constructors._
import purescala.Expressions._
import purescala.ExprOps._
import purescala.Types._
import utils._

import z3.FairZ3Component.{optFeelingLucky, optUseCodeGen, optAssumePre, optNoChecks, optUnfoldFactor}
import templates._
import evaluators._
import Template._

class UnrollingSolver(val context: LeonContext, val program: Program, underlying: Solver)
  extends Solver
     with NaiveAssumptionSolver
     with EvaluatingSolver
     with QuantificationSolver {

  val feelingLucky   = context.findOptionOrDefault(optFeelingLucky)
  val useCodeGen     = context.findOptionOrDefault(optUseCodeGen)
  val assumePreHolds = context.findOptionOrDefault(optAssumePre)
  val disableChecks  = context.findOptionOrDefault(optNoChecks)
  val unfoldFactor   = context.findOptionOrDefault(optUnfoldFactor)

  protected var lastCheckResult : (Boolean, Option[Boolean], Option[HenkinModel]) = (false, None, None)

  private val freeVars    = new IncrementalSet[Identifier]()
  private val constraints = new IncrementalSeq[Expr]()

  protected var interrupted : Boolean = false

  val reporter = context.reporter

  def name = "U:"+underlying.name

  def free() {
    underlying.free()
  }

  val templateGenerator = new TemplateGenerator(new TemplateEncoder[Expr] {
    def encodeId(id: Identifier): Expr= {
      Variable(id.freshen)
    }

    def encodeExpr(bindings: Map[Identifier, Expr])(e: Expr): Expr = {
      replaceFromIDs(bindings, e)
    }

    def substitute(substMap: Map[Expr, Expr]): Expr => Expr = {
      (e: Expr) => replace(substMap, e)
    }

    def mkNot(e: Expr) = not(e)
    def mkOr(es: Expr*) = orJoin(es)
    def mkAnd(es: Expr*) = andJoin(es)
    def mkEquals(l: Expr, r: Expr) = Equals(l, r)
    def mkImplies(l: Expr, r: Expr) = implies(l, r)
  }, assumePreHolds)

  val unrollingBank = new UnrollingBank(context, templateGenerator)

  val solver = underlying

  def assertCnstr(expression: Expr) {
    constraints += expression

    val freeIds = variablesOf(expression)

    freeVars ++= freeIds

    val newVars = freeIds.map(_.toVariable: Expr)

    val bindings = newVars.zip(newVars).toMap

    val newClauses = unrollingBank.getClauses(expression, bindings)

    for (cl <- newClauses) {
      solver.assertCnstr(cl)
    }
  }

  override def dbg(msg: => Any) = underlying.dbg(msg)

  def push() {
    unrollingBank.push()
    solver.push()
    freeVars.push()
    constraints.push()
  }

  def pop() {
    unrollingBank.pop()
    solver.pop()
    freeVars.pop()
    constraints.pop()
  }

  def check: Option[Boolean] = {
    genericCheck(Set())
  }

  def hasFoundAnswer = lastCheckResult._1

  private def extractModel(model: Model): HenkinModel = {
    val allVars = freeVars.toSet

    def extract(b: Expr, m: Matcher[Expr]): Set[Seq[Expr]] = {
      val QuantificationTypeMatcher(fromTypes, _) = m.tpe
      val optEnabler = evaluator.eval(b, model).result

      if (optEnabler == Some(BooleanLiteral(true))) {
        val optArgs = m.args.map(arg => evaluator.eval(arg.encoded, model).result)
        if (optArgs.forall(_.isDefined)) {
          Set(optArgs.map(_.get))
        } else {
          Set.empty
        }
      } else {
        Set.empty
      }
    }

    val (typeInsts, partialInsts, lambdaInsts) = templateGenerator.manager.instantiations

    val typeDomains: Map[TypeTree, Set[Seq[Expr]]] = typeInsts.map {
      case (tpe, domain) => tpe -> domain.flatMap { case (b, m) => extract(b, m) }.toSet
    }

    val funDomains: Map[Identifier, Set[Seq[Expr]]] = partialInsts.map {
      case (Variable(id), domain) => id -> domain.flatMap { case (b, m) => extract(b, m) }.toSet
    }

    val lambdaDomains: Map[Lambda, Set[Seq[Expr]]] = lambdaInsts.map {
      case (l, domain) => l -> domain.flatMap { case (b, m) => extract(b, m) }.toSet
    }

    val asDMap = purescala.Quantification.extractModel(model.toMap, funDomains, typeDomains, evaluator)
    val domains = new HenkinDomains(lambdaDomains, typeDomains)
    new HenkinModel(asDMap, domains)
  }

  def foundAnswer(res: Option[Boolean], model: Option[HenkinModel] = None) = {
    lastCheckResult = (true, res, model)
  }

  def validatedModel(silenceErrors: Boolean = false): (Boolean, HenkinModel) = {
    val lastModel = solver.getModel
    val clauses = templateGenerator.manager.checkClauses
    val optModel = if (clauses.isEmpty) Some(lastModel) else {
      solver.push()
      for (clause <- clauses) {
        solver.assertCnstr(clause)
      }

      reporter.debug(" - Verifying model transitivity")
      val solverModel = solver.check match {
        case Some(true) =>
          Some(solver.getModel)

        case Some(false) =>
          val msg = "- Transitivity independence not guaranteed for model"
          if (silenceErrors) {
            reporter.debug(msg)
          } else {
            reporter.warning(msg)
          }
          None

        case None =>
          val msg = "- Unknown for transitivity independence!?"
          if (silenceErrors) {
            reporter.debug(msg)
          } else {
            reporter.warning(msg)
          }
          None
      }

      solver.pop()
      solverModel
    }

    optModel match {
      case None =>
        (false, extractModel(lastModel))

      case Some(m) =>
        val model = extractModel(m)

        val expr = andJoin(constraints.toSeq)
        val fullModel = model set freeVars.toSet

        (evaluator.check(expr, fullModel) match {
          case EvaluationResults.CheckSuccess =>
            reporter.debug("- Model validated.")
            true

          case EvaluationResults.CheckValidityFailure =>
            reporter.debug("- Invalid model.")
            false

          case EvaluationResults.CheckRuntimeFailure(msg) =>
            if (silenceErrors) {
              reporter.debug("- Model leads to evaluation error: " + msg)
            } else {
              reporter.warning("- Model leads to evaluation error: " + msg)
            }
            false

          case EvaluationResults.CheckQuantificationFailure(msg) =>
            if (silenceErrors) {
              reporter.debug("- Model leads to quantification error: " + msg)
            } else {
              reporter.warning("- Model leads to quantification error: " + msg)
            }
            false
        }, fullModel)
    }
  }

  def genericCheck(assumptions: Set[Expr]): Option[Boolean] = {
    lastCheckResult = (false, None, None)

    while(!hasFoundAnswer && !interrupted) {
      reporter.debug(" - Running search...")

      solver.push()
      solver.assertCnstr(andJoin((assumptions ++ unrollingBank.satisfactionAssumptions).toSeq))
      val res = solver.check

      reporter.debug(" - Finished search with blocked literals")

      res match {
        case None =>
          solver.pop()

          reporter.ifDebug { debug =>
            reporter.debug("Solver returned unknown!?")
          }
          foundAnswer(None)

        case Some(true) => // SAT
          val (valid, model) = if (!this.disableChecks && requireQuantification) {
            validatedModel(silenceErrors = false)
          } else {
            true -> extractModel(solver.getModel)
          }

          solver.pop()
          if (valid) {
            foundAnswer(Some(true), Some(model))
          } else {
            reporter.error("Something went wrong. The model should have been valid, yet we got this : ")
            reporter.error(model.asString(context))
            foundAnswer(None, Some(model))
          }

        case Some(false) if !unrollingBank.canUnroll =>
          solver.pop()
          foundAnswer(Some(false))

        case Some(false) =>
          //debug("UNSAT BECAUSE: "+solver.getUnsatCore.mkString("\n  AND  \n"))
          //debug("UNSAT BECAUSE: "+core.mkString("  AND  "))
          solver.pop()

          if (!interrupted) {
            if (feelingLucky) {
              reporter.debug(" - Running search without blocked literals (w/ lucky test)")
            } else {
              reporter.debug(" - Running search without blocked literals (w/o lucky test)")
            }

            solver.push()
            solver.assertCnstr(andJoin(assumptions.toSeq ++ unrollingBank.refutationAssumptions))
            val res2 = solver.check

            res2 match {
              case Some(false) =>
                //reporter.debug("UNSAT WITHOUT Blockers")
                foundAnswer(Some(false))

              case Some(true) =>
                if (feelingLucky && !interrupted) {
                  // we might have been lucky :D
                  val (valid, model) = validatedModel(silenceErrors = true)
                  if (valid) foundAnswer(Some(true), Some(model))
                }

              case None =>
                foundAnswer(None)
            }
            solver.pop()
          }

          if(interrupted) {
            foundAnswer(None)
          }

          if(!hasFoundAnswer) {
            reporter.debug("- We need to keep going.")

            // unfolling `unfoldFactor` times
            for (i <- 1 to unfoldFactor.toInt) {
              val toRelease = unrollingBank.getBlockersToUnlock

              reporter.debug(" - more unrollings")

              val newClauses = unrollingBank.unrollBehind(toRelease)

              for (ncl <- newClauses) {
                solver.assertCnstr(ncl)
              }
            }

            reporter.debug(" - finished unrolling")
          }
      }
    }

    if(interrupted) {
      None
    } else {
      lastCheckResult._2
    }
  }

  def getModel: HenkinModel = {
    lastCheckResult match {
      case (true, Some(true), Some(m)) =>
        m.filter(freeVars.toSet)
      case _ =>
        HenkinModel.empty
    }
  }

  override def reset() = {
    underlying.reset()
    lastCheckResult  = (false, None, None)
    freeVars.reset()
    constraints.reset()
    interrupted      = false
  }

  override def interrupt(): Unit = {
    interrupted = true
    solver.interrupt()
  }

  override def recoverInterrupt(): Unit = {
    solver.recoverInterrupt()
    interrupted = false
  }
}
