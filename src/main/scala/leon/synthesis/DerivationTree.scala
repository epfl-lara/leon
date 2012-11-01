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

    def printTask(t: SimpleTask) {

      val node = nameFor(t, "task");

      t.solverTask match {
        case Some(decompTask) =>
          res append " "+node+" [ label = <<TABLE BORDER=\"0\" CELLBORDER=\"1\" CELLSPACING=\"0\"><TR><TD BORDER=\"0\">"+decompTask.rule.name+"</TD></TR><TR><TD BGCOLOR=\"indianred1\">"+escapeHTML(t.problem.toString)+"</TD></TR><TR><TD BGCOLOR=\"greenyellow\">"+escapeHTML(t.solution.map(_.toString).getOrElse("?"))+"</TD></TR></TABLE>> shape = \"none\" ];\n"

          for (t <- decompTask.subTasks) {
            printTask(t)
            res append nameFor(t, "task") +" -> " + " "+node+";\n"
          }

        case None =>
      }
    }


    printTask(root)

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
