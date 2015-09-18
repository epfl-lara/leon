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

import z3.FairZ3Component.{optFeelingLucky, optUseCodeGen, optAssumePre}
import templates._
import utils.Interruptible
import evaluators._

class UnrollingSolver(val context: LeonContext, val program: Program, underlying: Solver)
  extends Solver
     with NaiveAssumptionSolver
     with EvaluatingSolver
     with QuantificationSolver {

  val feelingLucky   = context.findOptionOrDefault(optFeelingLucky)
  val useCodeGen     = context.findOptionOrDefault(optUseCodeGen)
  val assumePreHolds = context.findOptionOrDefault(optAssumePre)

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
      val optEnabler = evaluator.eval(b).result
      if (optEnabler == Some(BooleanLiteral(true))) {
        val optArgs = m.args.map(arg => evaluator.eval(Matcher.argValue(arg)).result)
        if (optArgs.forall(_.isDefined)) {
          Set(optArgs.map(_.get))
        } else {
          Set.empty
        }
      } else {
        Set.empty
      }
    }

    val funDomains = allVars.flatMap(id => id.getType match {
      case ft @ FunctionType(fromTypes, _) =>
        Some(id -> templateGenerator.manager.instantiations(Variable(id), ft).flatMap {
          case (b, m) => extract(b, m)
        })
      case _ => None
    }).toMap.mapValues(_.toSet)

    val asDMap = model.map(p => funDomains.get(p._1) match {
      case Some(domain) =>
        val mapping = domain.toSeq.map { es =>
          val ev: Expr = p._2 match {
            case RawArrayValue(_, mapping, dflt) =>
              mapping.collectFirst {
                case (k,v) if evaluator.eval(Equals(k, tupleWrap(es))).result == Some(BooleanLiteral(true)) => v
              } getOrElse dflt
            case _ => scala.sys.error("Unexpected function encoding " + p._2)
          }
          es -> ev
        }

        p._1 -> PartialLambda(mapping, p._1.getType.asInstanceOf[FunctionType])
      case None => p
    }).toMap

    val typeGrouped = templateGenerator.manager.instantiations.groupBy(_._2.tpe)
    val typeDomains = typeGrouped.mapValues(_.flatMap { case (b, m) => extract(b, m) }.toSet)

    val domains = new HenkinDomains(typeDomains)
    new HenkinModel(asDMap, domains)
  }

  def foundAnswer(res: Option[Boolean], model: Option[HenkinModel] = None) = {
    lastCheckResult = (true, res, model)
  }

  def isValidModel(model: HenkinModel, silenceErrors: Boolean = false): Boolean = {
    import EvaluationResults._

    val expr = andJoin(constraints.toSeq)
    val fullModel = model fill freeVars.toSet

    evaluator.eval(expr, fullModel) match {
      case Successful(BooleanLiteral(true)) =>
        reporter.debug("- Model validated.")
        true

      case Successful(BooleanLiteral(false)) =>
        reporter.debug("- Invalid model.")
        false

      case Successful(e) =>
        reporter.warning("- Model leads unexpected result: "+e)
        false

      case RuntimeError(msg) =>
        reporter.debug("- Model leads to runtime error.")
        false

      case EvaluatorError(msg) => 
        if (silenceErrors) {
          reporter.debug("- Model leads to evaluator error: " + msg)
        } else {
          reporter.warning("- Model leads to evaluator error: " + msg)
        }
        false
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
          val model = extractModel(solver.getModel)
          solver.pop()
          foundAnswer(Some(true), Some(model))

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
                  val model = extractModel(solver.getModel)

                  // we might have been lucky :D
                  if (isValidModel(model, silenceErrors = true)) {
                    foundAnswer(Some(true), Some(model))
                  }
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

            val toRelease = unrollingBank.getBlockersToUnlock

            reporter.debug(" - more unrollings")

            val newClauses = unrollingBank.unrollBehind(toRelease)

            for(ncl <- newClauses) {
              solver.assertCnstr(ncl)
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
