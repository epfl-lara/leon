/* Copyright 2009-2014 EPFL, Lausanne */

package leon
package solvers
package combinators

import purescala.Common._
import purescala.Definitions._
import purescala.Trees._
import purescala.TreeOps._
import purescala.TypeTrees._

import solvers.templates._
import utils.Interruptible
import evaluators._

class UnrollingSolver(val context: LeonContext, program: Program, underlying: IncrementalSolver) extends Solver with Interruptible {

  val (feelingLucky, useCodeGen) = locally {
    var lucky            = false
    var codegen          = false

    for(opt <- context.options) opt match {
      case LeonFlagOption("feelinglucky", v)       => lucky   = v
      case LeonFlagOption("codegen", v)            => codegen = v
      case _ =>
    }

    (lucky, codegen)
  }

  private val evaluator : Evaluator = {
    if(useCodeGen) {
      new CodeGenEvaluator(context, program)
    } else {
      new DefaultEvaluator(context, program)
    }
  }

  private var lastCheckResult: (Boolean, Option[Boolean], Option[Map[Identifier,Expr]]) = (false, None, None)
  private var varsInVC       = List[Set[Identifier]](Set())
  private var constraints    = List[List[Expr]](Nil)
  private var interrupted: Boolean = false

  val reporter = context.reporter

  def name = "U:"+underlying.name

  def free {}


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

    def not(e: Expr) = Not(e)
    def implies(l: Expr, r: Expr) = Implies(l, r)
  })

  val unrollingBank = new UnrollingBank(reporter, templateGenerator)

  val solver = underlying

  def assertCnstr(expression: Expr) {
    val freeIds = variablesOf(expression)

    val freeVars = freeIds.map(_.toVariable: Expr)

    val bindings = freeVars.zip(freeVars).toMap

    val newClauses = unrollingBank.getClauses(expression, bindings)

    for (cl <- newClauses) {
      solver.assertCnstr(cl)
    }

    varsInVC    = (varsInVC.head ++ freeIds) :: varsInVC.tail
    constraints = (constraints.head ++ newClauses) :: constraints.tail
  }


  def push() {
    unrollingBank.push()
    solver.push()
    varsInVC = Set[Identifier]() :: varsInVC
    constraints = Nil :: constraints
  }

  def pop(lvl: Int = 1) {
    unrollingBank.pop(lvl)
    solver.pop(lvl)
    varsInVC = varsInVC.drop(lvl)
    constraints = constraints.drop(lvl)
  }

  def check: Option[Boolean] = {
    genericCheck(Set())
  }

  def hasFoundAnswer = lastCheckResult._1

  def foundAnswer(res: Option[Boolean], model: Option[Map[Identifier, Expr]] = None) = {
    lastCheckResult = (true, res, model)
  }

  def isValidModel(model: Map[Identifier, Expr], silenceErrors: Boolean = false): Boolean = {
    import EvaluationResults._

    val expr = And(constraints.flatten)

    val fullModel = variablesOf(expr).map(v => v -> model.getOrElse(v, simplestValue(v.getType))).toMap

    evaluator.eval(expr, fullModel) match {
      case Successful(BooleanLiteral(true)) =>
        reporter.debug("- Model validated.")
        true

      case Successful(BooleanLiteral(false)) =>
        reporter.debug("- Invalid model.")
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
      solver.assertCnstr(And((assumptions ++ unrollingBank.currentBlockers).toSeq))
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
          val model = solver.getModel
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
            solver.assertCnstr(And(assumptions.toSeq))
            val res2 = solver.check

            res2 match {
              case Some(false) =>
                //reporter.debug("UNSAT WITHOUT Blockers")
                foundAnswer(Some(false))

              case Some(true) =>
                if (feelingLucky && !interrupted) {
                  val model = solver.getModel

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

  def getModel: Map[Identifier,Expr] = {
    val allVars = varsInVC.flatten.toSet
    lastCheckResult match {
      case (true, Some(true), Some(m)) =>
        m.filterKeys(allVars)
      case _ =>
        Map()
    }
  }

  override def interrupt(): Unit = {
    interrupted = true
  }

  override def recoverInterrupt(): Unit = {
    interrupted = false
  }
}
