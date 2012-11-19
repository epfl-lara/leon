package leon
package synthesis

class DerivationTree(root: RootTask)  {

  private[this] var _nextID = 0

  def nextID = {
    _nextID += 1
    _nextID
  }

  def escapeHTML(str: String) = str.replaceAll("<", "&lt;").replaceAll(">", "&gt;")

  def toDot: String = {
    val res = new StringBuffer()

    res append "digraph D {\n"
    res append " label=\"Derivation Tree\"\n"
//    res append " rankdir=\"LR\"\n"

    var taskNames = Map[Task, String]()
    def taskName(t: Task) = {
      taskNames.get(t) match {
        case Some(name) =>
          name
        case None =>
          val name = "task"+nextID
          taskNames += t -> name
          name
      }
    }

    def printTask(t: Task) {

      val node = taskName(t);

      res append " "+node+" [ label = <<TABLE BORDER=\"0\" CELLBORDER=\"1\" CELLSPACING=\"0\"><TR><TD BORDER=\"0\">"+t.rule+"</TD></TR><TR><TD BGCOLOR=\"indianred1\">"+escapeHTML(t.problem.toString)+"</TD></TR><TR><TD BGCOLOR=\"greenyellow\">"+escapeHTML(t.solution.map(_.toString).getOrElse("?"))+"</TD></TR></TABLE>> shape = \"none\" ];\n"

      for (st <- t.solver.map(_.allSteps).flatten.flatMap(_.subSolvers.values)) {
        res.append(" "+taskName(st)+" -> "+node+"\n")
        printTask(st)
      }

    }


    root.solverTask.foreach(printTask)

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
