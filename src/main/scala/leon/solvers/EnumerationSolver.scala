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

class EnumerationSolver(val context: LeonContext, val program: Program) extends Solver with Interruptible with IncrementalSolver with NaiveAssumptionSolver {
  def name = "Enum"

  val maxTried = 10000

  var datagen: Option[DataGenerator] = None

  private var interrupted = false

  var freeVars    = List[List[Identifier]](Nil)
  var constraints = List[List[Expr]](Nil)

  def assertCnstr(expression: Expr): Unit = {
    constraints = (constraints.head :+ expression) :: constraints.tail

    val newFreeVars = (variablesOf(expression) -- freeVars.flatten).toList

    freeVars = (freeVars.head ::: newFreeVars) :: freeVars.tail
  }

  def push() = {
    freeVars = Nil :: freeVars
    constraints = Nil :: constraints
  }

  def pop(lvl: Int) = {
    freeVars = freeVars.drop(lvl)
    constraints = constraints.drop(lvl)
  }

  private var modelMap = Map[Identifier, Expr]()

  def check: Option[Boolean] = {
    val timer = context.timers.solvers.enum.check.start()
    val res = try {
      datagen = Some(new VanuatooDataGen(context, program))
      if (interrupted) {
        None
      } else {
        modelMap = Map()
        val allFreeVars = freeVars.reverse.flatten
        val allConstraints = constraints.reverse.flatten

        val it = datagen.get.generateFor(allFreeVars, andJoin(allConstraints), 1, maxTried)

        if (it.hasNext) {
          val model = it.next
          modelMap = (allFreeVars zip model).toMap
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

  def getModel: Map[Identifier, Expr] = {
    modelMap
  }

  def free() = {
    constraints = Nil
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
