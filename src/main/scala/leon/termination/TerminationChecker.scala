/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package termination

import purescala.Definitions._
import purescala.Expressions._
import purescala.DefOps._

abstract class TerminationChecker(val context: LeonContext, val program: Program) extends LeonComponent {

  val functions = visibleFunDefsFromMain(program)

  def terminates(funDef : FunDef) : TerminationGuarantee
}

sealed abstract class TerminationGuarantee {
  def isGuaranteed: Boolean
}

abstract class Terminating(justification: String) extends TerminationGuarantee {
  override def isGuaranteed: Boolean = true
}

case class Terminates(justification: String) extends Terminating(justification)

abstract class NonTerminating extends TerminationGuarantee {
  override def isGuaranteed: Boolean = false
}

case class LoopsGivenInputs(justification: String, args: Seq[Expr]) extends NonTerminating
case class MaybeLoopsGivenInputs(justification: String, args: Seq[Expr]) extends NonTerminating

case class CallsNonTerminating(calls: Set[FunDef]) extends NonTerminating

case object NoGuarantee extends TerminationGuarantee {
  override def isGuaranteed: Boolean = false
}
