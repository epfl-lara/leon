/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package solvers
package smtlib

import purescala.Common.Tree

case class SMTLIBUnsupportedError(t: Tree, s: SMTLIBTarget, reason: Option[String] = None)
  extends Unsupported(t, s" is unsupported by ${s.targetName}" + reason.map(":\n  " + _ ).getOrElse(""))(s.context)
