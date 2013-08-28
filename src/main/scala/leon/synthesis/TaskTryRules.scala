package leon
package synthesis

import synthesis.search._

case class TaskTryRules(p: Problem) extends AOOrTask[Solution] {
  override def toString = p.toString
}
