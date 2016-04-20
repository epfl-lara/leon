/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package synthesis
package strategies

import purescala.Common.FreshIdentifier

import graph._

class ManualStrategy(ctx: LeonContext, initCmd: Option[String], strat: Strategy) extends Strategy {
  implicit val ctx_ = ctx

  import ctx.reporter._

  abstract class Command
  case class Cd(path: List[Int]) extends Command
  case object Parent extends Command
  case object Quit extends Command
  case object Noop extends Command
  case object Best extends Command
  case object Tree extends Command
  case object Help extends Command

  // Manual search state:
  var rootNode: Node    = _

  var path              = List[Int]()

  override def init(n: RootNode) = {
    super.init(n)
    strat.init(n)

    rootNode = n
  }

  def currentNode(path: List[Int]): Node = {
    def findFrom(n: Node, path: List[Int]): Node = {
      path match {
        case Nil => n
        case p :: ps =>
          findDescendent(n, p) match {
            case Some(d) =>
              findFrom(d, ps)
            case None =>
              n
          }
      }
    }

    findFrom(rootNode, path)
  }

  override def beforeExpand(n: Node) = {
    super.beforeExpand(n)
    strat.beforeExpand(n)
  }

  override def afterExpand(n: Node) = {
    super.afterExpand(n)
    strat.afterExpand(n)

    // Backtrack view to a point where node is neither closed nor solved
    if (n.isDeadEnd || n.isSolved) {
      val backtrackTo = findAncestor(n, n => !n.isDeadEnd && !n.isSolved)

      path = backtrackTo.map(pathTo).getOrElse(Nil)
    }
  }

  private def findAncestor(n: Node, f: Node => Boolean): Option[Node] = {
    n.parent.flatMap { n =>
      if (f(n)) Some(n) else findAncestor(n, f)
    }
  }

  private def pathTo(n: Node): List[Int] = {
    n.parent match {
      case None => Nil
      case Some(p) => pathTo(p) :+ p.descendants.indexOf(n)
    }
  }


  def bestAlternative(n: OrNode) = strat.bestAlternative(n)


  def printGraph() {
    def title(str: String)    = "\u001b[1m"  + str + "\u001b[0m"
    def failed(str: String)   = "\u001b[31m" + str + "\u001b[0m"
    def solved(str: String)   = "\u001b[32m" + str + "\u001b[0m"
    def expanded(str: String) = "\u001b[33m" + str + "\u001b[0m"

    def displayNode(n: Node, inTitle: Boolean = false): String = {
      n match {
        case an: AndNode =>
          val app = an.ri.asString(ctx)
          s"(${debugInfoFor(n)}) ${indent(app, inTitle)}"
        case on: OrNode =>
          val p = on.p.asString(ctx)
          s"(${debugInfoFor(n)}) ${indent(p, inTitle)}"
      }
    }

    def indent(a: String, inTitle: Boolean): String = {
      a.replaceAll("\n", "\n"+(" "*(if(inTitle) 11 else 13)))
    }

    def pathToString(cd: List[Int]): String = {
      cd.map(i => f"$i%2d").mkString(" ")
    }

    val c = currentNode(path)

    println("-"*120)
    val at = path.lastOption.map(p => pathToString(List(p))).getOrElse(" R")

    println(title(at+" \u2510 "+displayNode(c, true)))

    for ((sn, i) <- c.descendants.zipWithIndex) {
      val sp = List(i)

      if (sn.isSolved) {
        println(solved("  "+pathToString(sp)+" \u2508 "+displayNode(sn)))
      } else if (sn.isDeadEnd) {
        println(failed("  "+pathToString(sp)+" \u2508 "+displayNode(sn)))
      } else if (sn.isExpanded) {
        println(expanded("  "+pathToString(sp)+" \u2508 "+displayNode(sn)))
      } else {
        println("  "+pathToString(sp)+" \u2508 "+displayNode(sn))
      }
    }
    println("-"*120)
  }

  var continue = true

  def findDescendent(n: Node, index: Int): Option[Node] = {
    n.descendants.zipWithIndex.find(_._2 == index).map(_._1)
  }

  def manualGetNext(): Option[Node] = {
    val c = currentNode(path)

    if (!c.isExpanded) {
      Some(c)
    } else {
      printGraph()

      nextCommand() match {
        case Quit =>
          None

        case Help =>
          val tOpen  = "\u001b[1m"
          val tClose = "\u001b[0m"
          println(s"""|
                      |${tOpen}Available commands: $tClose
                      |$tOpen  (cd) N  $tClose  Expand descendant N
                      |$tOpen  cd ..   $tClose  Go one level up
                      |$tOpen  b       $tClose  Expand best descendant
                      |$tOpen  t       $tClose  Display the partial solution around the current node
                      |$tOpen  q       $tClose  Quit the search
                      |$tOpen  h       $tClose  Display this message
                      |""".stripMargin)
          manualGetNext()
        case Parent =>
          if (path.nonEmpty) {
            path = path.dropRight(1)
          } else {
            error("Already at root node!")
          }

          manualGetNext()

        case Tree =>
          val hole = FreshIdentifier("\u001b[1;31m??? \u001b[0m", c.p.outType)
          val ps = new PartialSolution(this, true)

          ps.solutionAround(c)(hole.toVariable) match {
            case Some(sol) =>
              println("-"*120)
              println(sol.toExpr.asString)
            case None =>
              error("woot!")
          }
          manualGetNext()

        case Best =>
          strat.bestNext(c) match {
            case Some(n) =>
              val i = c.descendants.indexOf(n)
              path = path :+ i
              Some(currentNode(path))

            case None =>
              error("Woot?")
              manualGetNext()
          }


        case Cd(Nil) =>
          error("Woot?")
          None

        case Cd(next :: rest) =>
          findDescendent(c, next) match {
            case Some(_) =>
              path = path :+ next
            case None =>
              warning("Unknown descendant: "+next)
          }

          if (rest.nonEmpty) {
            cmdQueue = Cd(rest) :: cmdQueue
          }
          manualGetNext()
      }
    }
  }

  override def getNextToExpand(root: Node): Option[Node] = {
    manualGetNext()
  }

  def debugInfoFor(n: Node) = strat.debugInfoFor(n)

  var cmdQueue = initCmd.map( str => parseCommands(parseString(str))).getOrElse(Nil)

  private def parseString(s: String): List[String] = {
    Option(s).map(_.trim.split("\\s+|,").toList).getOrElse(fatalError("End of stream"))
  }

  private def nextCommand(): Command = cmdQueue match {
    case c :: cs =>
      cmdQueue = cs
      c

    case Nil =>
      print("Next action? (h for help) "+path.mkString(" ")+" $ ")
      val line = scala.io.StdIn.readLine()
      val parts = parseString(line)

      cmdQueue = parseCommands(parts)
      nextCommand()
  }

  private def parseCommands(tokens: List[String]): List[Command] = tokens match {
    case "cd" :: ".." :: ts =>
      Parent :: parseCommands(ts)

    case "cd" :: ts =>
      val path = ts.takeWhile { t => t.forall(_.isDigit) }

      if (path.isEmpty) {
        parseCommands(ts)
      } else {
        Cd(path.map(_.toInt)) :: parseCommands(ts.drop(path.size))
      }

    case "t" :: ts =>
      Tree :: parseCommands(ts)

    case "b" :: ts =>
      Best :: parseCommands(ts)

    case "h" :: ts =>
      Help :: parseCommands(ts)

    case "q" :: ts =>
      Quit :: Nil

    case Nil  | "" :: Nil =>
      Nil

    case ts =>
      val path = ts.takeWhile { t => t.forall(_.isDigit) }

      if (path.isEmpty) {
        error("Unknown command "+ts.head)
        parseCommands(ts.tail)
      } else {
        Cd(path.map(_.toInt)) :: parseCommands(ts.drop(path.size))
      }
  }
}
