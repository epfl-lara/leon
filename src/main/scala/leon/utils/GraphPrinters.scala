/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package utils

import Graphs._

object GraphPrinters {
  abstract class Printer[N, E <: EdgeLike[N], G <: DiGraphLike[N, E, G]] {

    def asString(g: G): String

    def asFile(g: G, file: String) {
      import java.io.{BufferedWriter, FileWriter}
      val out = new BufferedWriter(new FileWriter(file))
      out.write(asString(g))
      out.close()
    }
  }

  case class DotNode(label: String, opts: Map[String, String] = Map()) {
    def toOpts(dot: DotHelpers): String = {
      s"""[label="${dot.escape(label)}"]"""
    }
  }

  class DotPrinter[N, E <: EdgeLike[N], G <: DiGraphLike[N, E, G]] extends Printer[N, E, G] {

    val dot = new DotHelpers

    private var nToLabel: N => String = { (n: N) => n.toString }

    private var nToOpts: Seq[N => Seq[(String, String)]] = Nil

    def setNodeLabel(f: N => String): Unit = {
      nToLabel = f
    }

    def colorize(f: N => Boolean, color: String) = {
      nToOpts :+= { (n: N) =>
        if (f(n)) List(("color", color)) else Nil
      }
    }

    def highlight(f: N => Boolean) = colorize(f, "red")


    def drawNode(n: N)(implicit res: StringBuffer): Unit = {
      var opts = Map[String, String]()
      opts += "label" -> ("\"" + dot.escape(nToLabel(n)) + "\"")

      for (f <- nToOpts) {
        opts ++= f(n)
      }

      res append (nToS(n) +" "+opts.map{ case (n, v) => s"$n=$v" }.mkString("[", ", ", "]")+";\n")
    }

    def nToS(n: N): String = {
      dot.uniqueName("n", n)
    }

    def eToS(e: EdgeLike[N]): String = {
      dot.uniqueName("e", e)
    }

    def drawEdge(e: E)(implicit res: StringBuffer): Unit = {
      e match {
        case le: LabeledEdge[_, N] =>
          res append dot.box(eToS(e), le.l.toString)
          res append dot.arrow(nToS(e._1), eToS(e))
          res append dot.arrow(eToS(e), nToS(e._2))
        case _ =>
          res append dot.arrow(nToS(e._1), nToS(e._2))
      }
    }

    def asString(g: G): String = {
      implicit val res = new StringBuffer()

      res append "digraph D {\n"

      g.N.foreach(drawNode)

      g.E.foreach(drawEdge)

      res append "}\n"

      res.toString
    }
  }

  class DotHelpers {
    private var _nextName   = 0
    private var _nextColor  = 0

    private def nextName = {
      _nextName += 1
      _nextName.toString
    }

    private var names = Map[Any, String]()

    def uniqueName(prefix: String, obj: Any) = {
      if (!names.contains(obj)) {
        names = names + (obj -> (prefix+nextName))
      }

      names(obj)
    }

    val bgColors = List("bisque", "khaki", "mistyrose", "lightcyan", "mediumorchid", "aquamarine", "antiquewhite")

    def nextColor = {
      _nextColor += 1
      val colornumber: String = if((_nextColor/bgColors.size)%3 == 0) "" else ((_nextColor/bgColors.size)%3)+"";
      bgColors(_nextColor%bgColors.size)+colornumber
    }

    val colors = List("khaki", "khaki1", "khaki2", "khaki3",
      "khaki4", "lavender", "lavenderblush", "lavenderblush1", "lavenderblush2",
      "lavenderblush3", "lavenderblush4", "lawngreen", "lemonchiffon",
      "lemonchiffon1", "lemonchiffon2", "lemonchiffon3", "lemonchiffon4",
      "lightblue", "lightblue1", "lightblue2", "lightblue3", "lightblue4",
      "lightcoral", "lightcyan", "lightcyan1", "lightcyan2", "lightcyan3",
      "lightcyan4", "lightgoldenrod", "lightgoldenrod1", "lightgoldenrod2",
      "lightgoldenrod3", "lightgoldenrod4", "lightgoldenrodyellow", "lightgray",
      "lightgrey", "lightpink", "lightpink1", "lightpink2", "lightpink3",
      "lightpink4", "lightsalmon", "lightsalmon1", "lightsalmon2", "lightsalmon3",
      "lightsalmon4", "lightseagreen", "lightskyblue", "lightskyblue1",
      "lightskyblue2", "lightskyblue3", "lightskyblue4", "lightslateblue",
      "lightslategray", "lightslategrey", "lightsteelblue", "lightsteelblue1",
      "lightsteelblue2", "lightsteelblue3", "lightsteelblue4", "lightyellow",
      "lightyellow1", "lightyellow2", "lightyellow3", "lightyellow4", "limegreen",
      "linen", "magenta", "magenta1", "magenta2", "magenta3", "magenta4", "maroon",
      "maroon1", "maroon2", "maroon3", "maroon4", "mediumaquamarine", "mediumblue",
      "mediumorchid", "mediumorchid1", "mediumorchid2", "mediumorchid3",
      "mediumorchid4", "mediumpurple", "mediumpurple1", "mediumpurple2",
      "mediumpurple3", "mediumpurple4", "mediumseagreen", "mediumslateblue",
      "mediumspringgreen", "mediumturquoise", "mediumvioletred", "midnightblue",
      "mintcream", "mistyrose", "mistyrose1", "mistyrose2", "mistyrose3",
      "mistyrose4", "moccasin", "navajowhite", "navajowhite1", "navajowhite2",
      "navajowhite3", "navajowhite4", "navy", "navyblue", "none", "oldlace",
      "olivedrab", "olivedrab1", "olivedrab2", "olivedrab3", "olivedrab4", "orange",
      "orange1", "orange2", "orange3", "orange4", "orangered", "orangered1",
      "orangered2", "orangered3", "orangered4", "orchid", "orchid1", "orchid2",
      "orchid3", "orchid4", "palegoldenrod", "palegreen", "palegreen1", "palegreen2",
      "palegreen3", "palegreen4", "paleturquoise", "paleturquoise1",
      "paleturquoise2", "paleturquoise3", "paleturquoise4", "palevioletred",
      "palevioletred1", "palevioletred2", "palevioletred3", "palevioletred4",
      "papayawhip", "peachpuff", "peachpuff1", "peachpuff2", "peachpuff3",
      "peachpuff4", "peru", "pink", "pink1", "pink2", "pink3", "pink4", "plum",
      "plum1", "plum2", "plum3", "plum4", "powderblue", "purple", "purple1",
      "purple2", "purple3", "purple4", "red", "red1", "red2", "red3", "red4",
      "rosybrown", "rosybrown1", "rosybrown2", "rosybrown3", "rosybrown4",
      "royalblue", "royalblue1", "royalblue2", "royalblue3", "royalblue4",
      "saddlebrown", "salmon", "salmon1", "salmon2", "salmon3", "salmon4",
      "sandybrown", "seagreen", "seagreen1", "seagreen2", "seagreen3", "seagreen4",
      "seashell", "seashell1", "seashell2", "seashell3", "seashell4", "sienna",
      "sienna1", "sienna2", "sienna3", "sienna4", "skyblue", "skyblue1", "skyblue2",
      "skyblue3", "skyblue4", "slateblue", "slateblue1", "slateblue2", "slateblue3",
      "slateblue4", "slategray", "slategray1", "slategray2", "slategray3",
      "slategray4", "slategrey", "snow", "snow1", "snow2", "snow3", "snow4",
      "springgreen", "springgreen1", "springgreen2", "springgreen3", "springgreen4",
      "steelblue", "steelblue1", "steelblue2", "steelblue3", "steelblue4", "tan",
      "tan1", "tan2", "tan3", "tan4", "thistle", "thistle1", "thistle2", "thistle3",
      "thistle4", "tomato", "tomato1", "tomato2", "tomato3", "tomato4",
      "transparent", "turquoise", "turquoise1", "turquoise2", "turquoise3",
      "turquoise4", "violet", "violetred", "violetred1", "violetred2", "violetred3",
      "violetred4", "wheat", "wheat1", "wheat2", "wheat3", "wheat4", "white",
      "whitesmoke", "yellow", "yellow1", "yellow2", "yellow3", "yellow4",
      "yellowgreen");

    def randomColor = {
      _nextColor += 1
      colors(_nextColor % colors.size)
    }

    def escape(s: String) =
      s.replaceAll("\\\\n", "__NEWLINE__")
       .replaceAll("\\\\", "\\\\\\\\")
       .replaceAll("\"", "\\\\\"")
       .replaceAll("\\\n", "\\\\n")
       .replaceAll("[^<>@a-zA-Z0-9;$.,!# \t=^:_\\\\\"'*+/&()\\[\\]{}\u03B5-]", "?")
       .replaceAll("__NEWLINE__", "\\\\n")

    def escapeStrict(s: String) = s.replaceAll("[^a-zA-Z0-9_]", "_")

    def labeledArrow(x: String, label: String, y: String, options: List[String] = Nil) =
      arrow(x, y, "label=\""+escape(label)+"\"" :: options)

    def labeledDashedArrow(x: String, label: String, y: String, options: List[String] = Nil) =
      arrow(x, y, "label=\""+escape(label)+"\"" :: "style=dashed" :: options)

    def arrow(x: String, y: String, options: List[String] = Nil) = {
      "  "+x+" -> "+y+options.mkString(" [", " ", "]")+";\n"
    }

    def box(id : String, name : String, options: List[String] = Nil) = {
      node(id, name, "shape=box" :: "color=lightblue" :: "style=filled" :: options)
    }

    def invisNode(id : String, name : String, options: List[String] = Nil) = {
      node(id, name, "shape=none" :: options)
    }

    def dashedNode(id : String, name : String, options: List[String] = Nil) = {
      node(id, name, "style=dashed" :: options)
    }

    def node(id: String, name: String, options: List[String] = Nil) = {
      id +("label=\""+escape(name)+"\"" :: options).mkString(" [", ", ", "]")+";\n"
    }
  }
}
