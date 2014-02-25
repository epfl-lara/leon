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

  var datagen: DataGenerator = _

  var freeVars    = List[Identifier]()
  var constraints = List[Expr]()

  def assertCnstr(expression: Expr): Unit = {
    constraints ::= expression

    val newFreeVars = (variablesOf(expression) -- freeVars).toList
    freeVars = freeVars ::: newFreeVars
  }

  private var modelMap = Map[Identifier, Expr]()

  def check: Option[Boolean] = {
    try { 
      val muteContext = context.copy(reporter = new DefaultReporter(context.settings))
      datagen = new VanuatooDataGen(muteContext, program)

      modelMap = Map()

      val it = datagen.generateFor(freeVars, And(constraints.reverse), 1, maxTried)

      if (it.hasNext) {
        val model = it.next
        modelMap = (freeVars zip model).toMap
        Some(true)
      } else {
        None
      }
    } catch {
      case e: codegen.CompilationException =>
        None
    }
  }

  def getModel: Map[Identifier, Expr] = {
    modelMap
  }

  def free() = {
    constraints = Nil
  }

  def interrupt(): Unit = {
    Option(datagen).foreach(_.interrupt)
  }

  def recoverInterrupt(): Unit = {
    Option(datagen).foreach(_.recoverInterrupt)
  }
}
