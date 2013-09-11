/* Copyright 2009-2013 EPFL, Lausanne */

package leon
package synthesis

import synthesis.search._

case class TaskRunRule(app: RuleInstantiation) extends AOAndTask[Solution] {

  val problem = app.problem
  val rule    = app.rule

  def composeSolution(sols: List[Solution]): Option[Solution] = {
    app.onSuccess(sols)
  }

  override def toString = rule.name
}
