/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package solvers

import purescala.Common.Tree

object SolverUnsupportedError {
  def msg(t: Tree, s: Solver, reason: Option[String]) = {
    s"(of ${t.getClass}) is unsupported by solver ${s.name}" + reason.map(":\n  " + _ ).getOrElse("")
  }
}

case class SolverUnsupportedError(t: Tree, s: Solver, reason: Option[String] = None)
  extends Unsupported(t, SolverUnsupportedError.msg(t,s,reason))(s.context)
