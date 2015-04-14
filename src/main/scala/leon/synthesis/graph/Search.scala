/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package synthesis
package graph

import scala.annotation.tailrec

import scala.collection.mutable.ArrayBuffer
import leon.utils.Interruptible
import java.util.concurrent.atomic.AtomicBoolean

abstract class Search(ctx: LeonContext, ci: ChooseInfo, p: Problem, costModel: CostModel) extends Interruptible {
  val g = new Graph(costModel, p)

  def findNodeToExpandFrom(n: Node): Option[Node]

  val interrupted = new AtomicBoolean(false)

  def doStep(n: Node, sctx: SynthesisContext): Unit = {
    ctx.timers.synthesis.step.timed {
      n match {
        case an: AndNode =>
          ctx.timers.synthesis.applications.get(an.ri.toString).timed {
            an.expand(SearchContext(sctx, ci, an, this))
          }

        case on: OrNode =>
          on.expand(SearchContext(sctx, ci, on, this))
      }
    }
  }

  @tailrec
  final def searchFrom(sctx: SynthesisContext, from: Node): Boolean = {
    findNodeToExpandFrom(from) match {
      case Some(n) =>
        doStep(n, sctx)

        if (from.isSolved) {
          true
        } else if (interrupted.get) {
          false
        } else {
          searchFrom(sctx, from)
        }
      case None =>
        false
    }
  }

  def traversePathFrom(n: Node, path: List[Int]): Option[Node] = path match {
    case Nil =>
      Some(n)
    case x :: xs =>
      if (n.isExpanded && n.descendents.size > x) {
        traversePathFrom(n.descendents(x), xs)
      } else {
        None
      }
  }

  def traversePath(path: List[Int]): Option[Node] = {
    traversePathFrom(g.root, path)
  }

  def search(sctx: SynthesisContext): Stream[Solution] = {
    if (searchFrom(sctx, g.root)) {
      g.root.generateSolutions()
    } else {
      Stream.empty
    }
  }

  def interrupt(): Unit = {
    interrupted.set(true)
  }

  def recoverInterrupt(): Unit = {
    interrupted.set(false)
  }

  ctx.interruptManager.registerForInterrupts(this)
}

class SimpleSearch(ctx: LeonContext, ci: ChooseInfo, p: Problem, costModel: CostModel, bound: Option[Int]) extends Search(ctx, ci, p, costModel) {
  val expansionBuffer = ArrayBuffer[Node]()

  def findIn(n: Node) {
    if (!n.isExpanded) {
      expansionBuffer += n
    } else if (!n.isDeadEnd) {
      n match {
        case an: AndNode =>
          an.descendents.foreach(findIn)

        case on: OrNode =>
          if (on.descendents.nonEmpty) {
            findIn(on.descendents.minBy(_.cost))
          }
      }
    }
  }

  var counter = 0

  def findNodeToExpandFrom(from: Node): Option[Node] = {
    counter += 1
    ctx.timers.synthesis.search.find.timed {
      if (!bound.isDefined || counter <= bound.get) {
        if (expansionBuffer.isEmpty) {
          findIn(from)
        }

        if (expansionBuffer.nonEmpty) {
          Some(expansionBuffer.remove(0))
        } else {
          None
        }
      } else {
        None
      }
    }
  }
}

class ManualSearch(ctx: LeonContext, ci: ChooseInfo, problem: Problem, costModel: CostModel, initCmd: Option[String]) extends Search(ctx, ci, problem, costModel) {
  import ctx.reporter._

  abstract class Command
  case class Cd(path: List[Int]) extends Command
  case object Parent extends Command
  case object Quit extends Command
  case object Noop extends Command

  // Manual search state:
  var cd       = List[Int]()
  var cmdQueue = initCmd.map( str => parseCommands(parseString(str))).getOrElse(Nil)

  def getNextCommand(): Command = cmdQueue match {
    case c :: cs =>
      cmdQueue = cs
      c

    case Nil =>
      print("Next action? (q to quit) "+cd.mkString(" ")+" $ ")
      val line = scala.io.StdIn.readLine()
      val parts = parseString(line)

      cmdQueue = parseCommands(parts)
      getNextCommand()
  }

  def parseString(s: String): List[String] = {
    s.trim.split("\\s+|,").toList
  }

  def parseCommands(tokens: List[String]): List[Command] = tokens match {
    case "cd" :: ".." :: ts =>
      Parent :: parseCommands(ts)

    case "cd" :: ts =>
      val path = ts.takeWhile { t => t.forall(_.isDigit) }

      if (path.isEmpty) {
        parseCommands(ts)
      } else {
        Cd(path.map(_.toInt)) :: parseCommands(ts.drop(path.size))
      }

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

  override def doStep(n: Node, sctx: SynthesisContext) = {
    super.doStep(n, sctx)

    // Backtrack view to a point where node is neither closed nor solved
    if (n.isDeadEnd || n.isSolved) {
      var from: Node = g.root
      var newCd = List[Int]()

      while (!from.isSolved && !from.isDeadEnd && newCd.size < cd.size) {
        val cdElem = cd(newCd.size)
        from = traversePathFrom(from, List(cdElem)).get
        if (!from.isSolved && !from.isDeadEnd) {
          newCd = cdElem :: newCd
        }
      }

      cd = newCd.reverse
    }
  }


  def printGraph() {
    def title(str: String)    = "\u001b[1m"  + str + "\u001b[0m"
    def failed(str: String)   = "\u001b[31m" + str + "\u001b[0m"
    def solved(str: String)   = "\u001b[32m" + str + "\u001b[0m"
    def expanded(str: String) = "\u001b[33m" + str + "\u001b[0m"

    def displayNode(n: Node): String = n match {
      case an: AndNode =>
        val app = an.ri
        s"(${n.cost.asString}) ${indent(app)}"
      case on: OrNode =>
        val p = on.p
        s"(${n.cost.asString}) ${indent(p)}"
    }

    def indent(a: Any): String = {
      a.toString.replaceAll("\n", "\n"+(" "*12))
    }

    def pathToString(cd: List[Int]): String = {
      cd.map(i => f"$i%2d").mkString(" ")
    }

    def displayPath(n: Node, cd: List[Int]) {
      if (cd.isEmpty) {
        println(title(pathToString(cd)+" \u2510 "+displayNode(n)))

        for ((sn, i) <- n.descendents.zipWithIndex) {
          val sp = cd ::: List(i)

          if (sn.isSolved) {
            println(solved(pathToString(sp)+" \u2508 "+displayNode(sn)))
          } else if (sn.isDeadEnd) {
            println(failed(pathToString(sp)+" \u2508 "+displayNode(sn)))
          } else if (sn.isExpanded) {
            println(expanded(pathToString(sp)+" \u2508 "+displayNode(sn)))
          } else {
            println(pathToString(sp)+" \u2508 "+displayNode(sn))
          }
        }
      } else {
        displayPath(n.descendents(cd.head), cd.tail)
      }
    }

    println("-"*120)
    displayPath(g.root, cd)
    println("-"*120)
  }

  var continue = true

  def findNodeToExpandFrom(from: Node): Option[Node] = {
    if (!from.isExpanded) {
      Some(from)
    } else {
      var res: Option[Option[Node]] = None

      while(res.isEmpty) {
        printGraph()

        try {
          getNextCommand() match {
            case Quit =>
              continue = false
              res = Some(None)
            case Parent =>
              if (cd.nonEmpty) {
                cd = cd.dropRight(1)
              } else {
                error("Already at root node")
              }

            case Cd(path) =>
              var currentNode = from
              var currentPath = cd ++ path
              cd = Nil
              while (currentPath.nonEmpty && currentNode.isExpanded && res.isEmpty) {
                traversePathFrom(currentNode, List(currentPath.head)) match {
                  case Some(n) =>
                    cd = cd ::: List(currentPath.head)
                    currentNode = n
                    currentPath = currentPath.tail

                  case None =>
                    warning("Unknown path: "+ (path mkString "/"))
                    //res = Some(None)
                    return findNodeToExpandFrom(from) 
                }
              }

              if (currentPath.nonEmpty) {
                cmdQueue = Cd(currentPath) :: cmdQueue
              }

              if (!currentNode.isExpanded) {
                res = Some(Some(currentNode))
              }
          }
        } catch {
          case e: java.lang.NumberFormatException =>

          case e: java.io.IOException =>
            continue = false

          case e: Throwable =>
            error("Woops: "+e.getMessage)
            e.printStackTrace()
        }
      }

      res.get
    }
  }
}
