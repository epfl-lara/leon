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

import scala.collection.mutable.{Map=>MutableMap}

class UnrollingSolver(val context: LeonContext, underlying: IncrementalSolver)
        extends Solver with Interruptible {

  private var lastCheckResult: (Boolean, Option[Boolean], Option[Map[Identifier,Expr]]) = (false, None, None)

  val reporter = context.reporter

  private var interrupted: Boolean = false

  def name = "U:"+underlying.name

  def free {}

  var varsInVC    = List[Set[Identifier]](Set())

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
  }


  def push() {
    unrollingBank.push()
    solver.push()
    varsInVC = Set[Identifier]() :: varsInVC
  }

  def pop(lvl: Int = 1) {
    unrollingBank.pop(lvl)
    solver.pop(lvl)
    varsInVC = varsInVC.drop(lvl)
  }

  def check: Option[Boolean] = {
    genericCheck(Set())
  }

  def hasFoundAnswer = lastCheckResult._1

  def foundAnswer(res: Option[Boolean], model: Option[Map[Identifier, Expr]] = None) = {
    lastCheckResult = (true, res, model)
  }

  def genericCheck(assumptions: Set[Expr]): Option[Boolean] = {
    lastCheckResult = (false, None, None)

    while(!hasFoundAnswer && !interrupted) {
      reporter.debug(" - Running search...")

      solver.push()
      solver.assertCnstr(And((assumptions ++ unrollingBank.currentBlockers).toSeq))
      val res = solver.check
      solver.pop()

      reporter.debug(" - Finished search with blocked literals")

      res match {
        case None =>
          reporter.ifDebug { debug =>
            reporter.debug("Solver returned unknown!?")
          }
          foundAnswer(None)

        case Some(true) => // SAT
          val model = solver.getModel

          foundAnswer(Some(true), Some(model))

        case Some(false) if !unrollingBank.canUnroll =>
          foundAnswer(Some(false))

        case Some(false) =>
          //debug("UNSAT BECAUSE: "+solver.getUnsatCore.mkString("\n  AND  \n"))
          //debug("UNSAT BECAUSE: "+core.mkString("  AND  "))

          if (!interrupted) {
            reporter.debug(" - Running search without blocked literals (w/o lucky test)")

            solver.push()
            solver.assertCnstr(And(assumptions.toSeq))
            val res2 = solver.check
            solver.pop()

            res2 match {
              case Some(false) =>
                //reporter.debug("UNSAT WITHOUT Blockers")
                foundAnswer(Some(false))

              case Some(true) =>

              case None =>
                foundAnswer(None)
            }
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
