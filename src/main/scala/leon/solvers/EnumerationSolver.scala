/* Copyright 2009-2013 EPFL, Lausanne */

package leon
package solvers

import utils._
import purescala.Common._
import purescala.Definitions._
import purescala.Trees._
import purescala.Extractors._
import purescala.TreeOps._
import purescala.TypeTrees._

import datagen._


class EnumerationSolver(val context: LeonContext, val program: Program) extends Solver with Interruptible {
  def name = "Enum"

  val maxTried = 10000;

  var datagen: Option[DataGenerator] = None

  private var interrupted = false;

  var freeVars    = List[Identifier]()
  var constraints = List[Expr]()

  def assertCnstr(expression: Expr): Unit = {
    constraints = constraints :+ expression

    val newFreeVars = (variablesOf(expression) -- freeVars).toList
    freeVars = freeVars ::: newFreeVars
  }

  private var modelMap = Map[Identifier, Expr]()

  def check: Option[Boolean] = {
    val res = try {
      datagen = Some(new VanuatooDataGen(context, program))
      if (interrupted) {
        None
      } else {
        modelMap = Map()

        val it = datagen.get.generateFor(freeVars, And(constraints), 1, maxTried)

        if (it.hasNext) {
          val model = it.next
          modelMap = (freeVars zip model).toMap
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
    res
  }

  def getModel: Map[Identifier, Expr] = {
    modelMap
  }

  def free() = {
    constraints = Nil
  }

  def interrupt(): Unit = {
    interrupted = true;

    datagen.foreach{ s =>
      s.interrupt
    }
  }

  def recoverInterrupt(): Unit = {
    datagen.foreach(_.recoverInterrupt)
  }
}
