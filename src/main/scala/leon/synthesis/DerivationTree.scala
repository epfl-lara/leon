package leon
package synthesis

class DerivationTree(root: RootTask)  {
  var store = Map[DecomposedTask, Map[Problem, DecomposedTask]]().withDefaultValue(Map())
  var solutions = Map[Task, Solution]()

  def recordSolutionFor(task: Task, solution: Solution) = task match {
    case dt: DecomposedTask =>
      if (dt.parent ne null) {
        store += dt.parent -> (store(dt.parent) + (task.problem -> dt))
      }

      solutions += dt -> solution
    case _ =>
  }

  private[this] var _nextID = 0

  def nextID = {
    _nextID += 1
    _nextID
  }

  def toDot: String = {
    val res = new StringBuffer()

    res append "digraph D {\n"
    res append " label=\"Derivation Tree\"\n"
//    res append " rankdir=\"LR\"\n"

    var namesCache = Map[(AnyRef, String), String]()
    def nameFor(t: AnyRef, prefix: String) = {
      namesCache.get((t, prefix)) match {
        case Some(name) =>
          name
        case None =>
          val name = prefix+nextID
          namesCache += ((t, prefix)) -> name
          name
      }
    }

    def printTask(t: DecomposedTask) {

      val node = nameFor(t, "task");

      res append " "+node+" [ label = <<TABLE BORDER=\"0\" CELLBORDER=\"1\" CELLSPACING=\"0\"><TR><TD BORDER=\"0\">"+t.rule.name+"</TD></TR><TR><TD BGCOLOR=\"indianred1\">"+t.problem+"</TD></TR><TR><TD BGCOLOR=\"greenyellow\">"+solutions.getOrElse(t, "?")+"</TD></TR></TABLE>> shape = \"none\" ];\n"


      for ((_, task) <- store(t)) {
        res append nameFor(task, "task") +" -> " + " "+node+";\n"
      }
      
      for ((_, subt) <- store(t)) {
        printTask(subt)
      }
    }

    for (task <- store.keysIterator if task.parent eq null) {
      printTask(task)
    }

    res append "}\n"

    res.toString
  }

  def toDotFile(fname: String) {
    import java.io.{BufferedWriter, FileWriter}
    val out = new BufferedWriter(new FileWriter(fname))
    out.write(toDot)
    out.close()
  }

}
