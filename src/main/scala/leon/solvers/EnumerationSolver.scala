/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package solvers

import utils._
import purescala.Common._
import purescala.Definitions._
import purescala.Constructors._
import purescala.Expressions._
import purescala.ExprOps._

import datagen._

class EnumerationSolver(val context: LeonContext, val program: Program) extends Solver with NaiveAssumptionSolver {
  def name = "Enum"

  val maxTried = 10000

  var datagen: Option[DataGenerator] = None

  private var interrupted = false

  val freeVars    = new IncrementalSet[Identifier]()
  val constraints = new IncrementalSeq[Expr]()

  def assertCnstr(expression: Expr): Unit = {
    constraints += expression
    freeVars ++= variablesOf(expression)
  }

  def push() = {
    freeVars.push()
    constraints.push()
  }

  def pop() = {
    freeVars.pop()
    constraints.pop()
  }

  def reset() = {
    freeVars.clear()
    constraints.clear()
    interrupted = false
    datagen     = None
  }

  private var model = Model.empty

  def check: Option[Boolean] = {
    val timer = context.timers.solvers.enum.check.start()
    val res = try {
      datagen = Some(new VanuatooDataGen(context, program))
      if (interrupted) {
        None
      } else {
        model = Model.empty
        val allFreeVars = freeVars.toSeq.sortBy(_.name)
        val allConstraints = constraints.toSeq

        val it = datagen.get.generateFor(allFreeVars, andJoin(allConstraints), 1, maxTried)

        if (it.hasNext) {
          val varModels = it.next
          model = new Model((allFreeVars zip varModels).toMap)
          Some(true)
        } else {
          None
        }
      }
    } catch {
      case e: codegen.CompilationException =>
        None
    }
    datagen = None
    timer.stop()
    res
  }

  def getModel: Model = {
    model
  }

  def free() = {
    constraints.clear()
  }

  def interrupt(): Unit = {
    interrupted = true

    datagen.foreach{ s =>
      s.interrupt
    }
  }

  def recoverInterrupt(): Unit = {
    datagen.foreach(_.recoverInterrupt)
  }
}
