package leon.synthesis.search


 class AndOrGraphDotConverter[AT <: AOAndTask[S],
                              OT <: AOOrTask[S],
                              S <: AOSolution](val g: AndOrGraph[AT, OT, S]) {


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
          drawOrNode(res, name, ot)
        case at: g.AndTree =>
          drawAndNode(res, name, at)
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
          for (sub <- (on.alternatives ++ on.triedAlternatives).values) {
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

  def drawOrNode(res: StringBuffer, name: String, t: g.OrTree) {
    val ot = t.task
    val (color, style) = t match {
      case l: g.OrLeaf =>
        (if (t.isSolved) "palegreen" else if (t.isUnsolvable) "firebrick" else "white" , "filled,dashed")
      case n: g.OrNode =>
        (if (t.isSolved) "palegreen" else if (t.isUnsolvable) "firebrick" else "white", "filled")
    }

    drawNode(res, name, t.minCost, ot.cost, ot.toString, color, style)
  }

  def drawNode(res: StringBuffer, name: String, allCost: Cost, selfCost: Cost, content: String, color: String, style: String) {
    res append "  "+name+" [label=\""+allCost.value+" | "+selfCost.value+" | "+content+"\", shape=box, fillcolor=\""+color+"\", style=\""+style+"\"]\n"
  }

  def drawAndNode(res: StringBuffer, name: String, t: g.AndTree) {
    val at = t.task
    val (color, style) = t match {
      case l: g.AndLeaf =>
        (if (t.isSolved) "palegreen" else if (t.isUnsolvable) "firebrick" else "white", "filled,dashed")
      case n: g.AndNode =>
        (if (t.isSolved) "palegreen" else if (t.isUnsolvable) "firebrick" else "white", "filled")
    }

    drawNode(res, name, t.minCost, at.cost, at.toString, color, style)
  }

  /** Writes the graph to a file readable with GraphViz. */
  def writeFile(fname: String) {
    import java.io.{BufferedWriter, FileWriter}
    val out = new BufferedWriter(new FileWriter(fname))
    out.write(toString)
    out.close()
  }
}
