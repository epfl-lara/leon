/* Copyright 2009-2014 EPFL, Lausanne */

package leon
package utils

import purescala.Trees._
import purescala.TypeTrees._
import purescala.Definitions._
import utils._

case class OracleTraverser(oracle: Expr, tpe: TypeTree, program: Program) {
  private def call(name: String) = {
    program.definedFunctions.find(_.id.name == "Oracle."+name) match {
      case Some(fd) =>
        FunctionInvocation(fd.typed(List(tpe)), List(oracle))
      case None =>
        sys.error("Unable to find Oracle."+name)
    }
  }

  def value: Expr = {
    call("head")
  }

  def left: OracleTraverser = {
    OracleTraverser(call("left"), tpe, program)
  }

  def right: OracleTraverser = {
    OracleTraverser(call("right"), tpe, program)
  }
}
