package leon
package synthesis

object Rules {
  def all = List()
}


abstract class Rule(val name: String) {
  def isApplicable(p: Problem, parent: Task): List[Task]
}
