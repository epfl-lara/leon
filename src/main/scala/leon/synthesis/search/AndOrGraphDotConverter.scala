/* Copyright 2009-2013 EPFL, Lausanne */

package leon.synthesis.search

class AndOrGraphDotConverter[AT <: AOAndTask[S],
                             OT <: AOOrTask[S],
                             S](val g: AndOrGraph[AT, OT, S], firstOnly: Boolean) {


  private[this] var _nextID = 0
  def freshName(prefix: String) = {
    _nextID += 1
    prefix+_nextID
  }

  override def toString: String = {
    val res = new StringBuffer()

    res append "digraph D {\n"

    // Print all nodes
    val (nodes, edges) = decomposeGraph

    var nodesToNames = Map[g.Tree, String]()

    for (n <- nodes) {
      val name = freshName("node")

      n match {
        case ot: g.OrTree =>
          drawNode(res, name, ot)
        case at: g.AndTree =>
          drawNode(res, name, at)
      }

      nodesToNames += n -> name
    }

    for ((f,t, isMin) <- edges) {
      val label = f match {
        case ot: g.OrTree =>
          "or"
        case at: g.AndTree =>
          ""
      }

      res append "  "+nodesToNames(f)+" -> "+nodesToNames(t) +"  [label=\""+label+"\""+(if (isMin) ", style=bold" else "")+"]\n";
    }

    res append "}\n"

    res.toString
  }

  def decomposeGraph: (Set[g.Tree], Set[(g.Tree, g.Tree, Boolean)]) = {
    var nodes = Set[g.Tree]()
    var edges = Set[(g.Tree, g.Tree, Boolean)]()

    def collect(n: g.Tree, wasMin: Boolean) {
      nodes += n

      n match {
        case an : g.AndNode =>
          for (sub <- an.subProblems.values) {
            edges += ((n, sub, wasMin))
            collect(sub, wasMin)
          }
        case on : g.OrNode =>
          val alternatives:Traversable[g.AndTree] = if (firstOnly) {
            Option(on.minAlternative)
          } else {
            on.alternatives.values
          }

          for (sub <- alternatives) {
            val isMin = sub == on.minAlternative
            edges += ((n, sub, isMin))
            collect(sub, isMin)
          }
        case _ =>
          // ignore leaves
      }
    }

    collect(g.tree, false)

    (nodes, edges)
  }


  def drawNode(res: StringBuffer, name: String, t: g.Tree) {

    def escapeHTML(str: String) = str.replaceAll("<", "&lt;").replaceAll(">", "&gt;")

    val (color, style) = t match {
      case l: g.Leaf =>
        (if (t.isSolved) "palegreen" else if (t.isUnsolvable) "firebrick" else "white" , "dashed")
      case n: g.Node[_] =>
        (if (t.isSolved) "palegreen" else if (t.isUnsolvable) "firebrick" else "white", "")
    }

    res append " "+name+" [ label = <<TABLE BORDER=\"0\" CELLBORDER=\"1\" CELLSPACING=\"0\"><TR><TD BORDER=\"0\">self: "+g.costModel.taskCost(t.task).value+" | tree-min: "+t.minCost.value+"</TD></TR><TR><TD BORDER=\"1\" BGCOLOR=\""+color+"\">"+escapeHTML(t.task.toString)+"</TD></TR>";

    if (t.isSolved) {
      res append "<TR><TD BGCOLOR=\""+color+"\">"+escapeHTML(t.solution.get.toString)+"</TD></TR>"
    }

    res append "</TABLE>>, shape = \"none\", style=\""+style+"\" ];\n"

  }

  /** Writes the graph to a file readable with GraphViz. */
  def writeFile(fname: String) {
    import java.io.{BufferedWriter, FileWriter}
    val out = new BufferedWriter(new FileWriter(fname))
    out.write(toString)
    out.close()
  }
}

object AndOrGraphDotConverterCounter {
  private var nextId = 0;
  def next() = {
    nextId += 1
    nextId
  }
}


