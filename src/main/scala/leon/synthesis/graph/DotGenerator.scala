/* Copyright 2009-2016 EPFL, Lausanne */

package leon.synthesis
package graph

import leon.utils.UniqueCounter

import java.io.{File, FileWriter, BufferedWriter}

class DotGenerator(search: Search) {
  implicit val ctx = search.ctx

  val g = search.g
  val strat = search.strat

  private val idCounter = new UniqueCounter[Unit]
  idCounter.nextGlobal // Start with 1

  def freshName(prefix: String) = {
    prefix + idCounter.nextGlobal
  }

  def writeFile(f: File): Unit = {
    val out = new BufferedWriter(new FileWriter(f))
    out.write(asString)
    out.close()
  }

  def writeFile(path: String): Unit = writeFile(new File(path))


  def asString: String = {
    val res = new StringBuffer()

    res append "digraph D {\n"

    // Print all nodes
    val edges = collectEdges(g.root)
    val nodes = edges.flatMap(e => Set(e._1, e._3))

    var nodesToNames = Map[Node, String]()

    for (n <- nodes) {
      val name = freshName("node")

      n match {
        case ot: OrNode =>
          drawNode(res, name, ot)
        case at: AndNode =>
          drawNode(res, name, at)
      }

      nodesToNames += n -> name
    }

    for ((f,i,t) <- edges) {
      val label = f match {
        case ot: OrNode =>
          "or"
        case at: AndNode =>
          i.toString
      }

      val style = if (f.selected contains t) {
        ", style=\"bold\""
      } else {
        ""
      }

      res append "  "+nodesToNames(f)+" -> "+nodesToNames(t) +"  [label=\""+label+"\""+style+"]\n"
    }

    res append "}\n"

    res.toString
  }

  def limit(o: Any, length: Int = 200): String = {
    val str = o.toString
    if (str.length > length) {
      str.substring(0, length-3)+"..."
    } else {
      str
    }
  }

  def nodeDesc(n: Node): String = n match {
    case an: AndNode => an.ri.asString
    case on: OrNode => on.p.asString
  }

  def drawNode(res: StringBuffer, name: String, n: Node) {

    val index = n.parent.map(_.descendants.indexOf(n) + " ").getOrElse("")

    def escapeHTML(str: String) = str.replaceAll("&", "&amp;").replaceAll("<", "&lt;").replaceAll(">", "&gt;")

    val color = if (n.isSolved) {
        "palegreen" 
      } else if (n.isDeadEnd) {
        "firebrick"
      } else if(n.isExpanded) {
        "grey80"
      } else {
        "white"
      }


    res append " "+name+" [ label = <<TABLE BORDER=\"0\" CELLBORDER=\"1\" CELLSPACING=\"0\">"
    
    res append "<TR><TD BORDER=\"0\">"+escapeHTML(strat.debugInfoFor(n))+"</TD></TR>"

    res append "<TR><TD BORDER=\"1\" BGCOLOR=\""+color+"\">"+escapeHTML(limit(index + nodeDesc(n)))+"</TD></TR>"

    if (n.isSolved) {
      res append "<TR><TD BGCOLOR=\""+color+"\">"+escapeHTML(limit(n.generateSolutions().head.asString))+"</TD></TR>"
    }

    res append "</TABLE>>, shape = \"none\" ];\n"

  }

  private def collectEdges(from: Node): Set[(Node, Int, Node)] = {
    from.descendants.zipWithIndex.flatMap { case (d, i) =>
      Set((from, i, d)) ++ collectEdges(d)
    }.toSet
  }
}

object dotGenIds extends UniqueCounter[Unit]
