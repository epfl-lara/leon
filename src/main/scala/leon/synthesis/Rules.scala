package leon
package synthesis

abstract class Rule(val name: String) {
  def isApplicable(p: Problem, parent: Task): List[Task]
}
