package leon
package synthesis
package graph

import scala.annotation.tailrec

import leon.utils.StreamUtils.cartesianProduct

import scala.collection.mutable.ArrayBuffer
import leon.utils.Interruptible
import java.util.concurrent.atomic.AtomicBoolean

abstract class Search(ctx: LeonContext, p: Problem, costModel: CostModel) extends Interruptible {
  val g = new Graph(p, costModel);

  import g.{Node, AndNode, OrNode, RootNode}

  def findNodeToExpandFrom(n: Node): Option[Node]

  val interrupted = new AtomicBoolean(false);

  def doStep(n: Node, sctx: SynthesisContext) = {
    n.expand(sctx)
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

class SimpleSearch(ctx: LeonContext, p: Problem, costModel: CostModel, bound: Option[Int]) extends Search(ctx, p, costModel) {
  import g.{Node, AndNode, OrNode, RootNode}

  val expansionBuffer = ArrayBuffer[Node]()

  def findIn(n: Node) {
    if (!n.isExpanded) {
      expansionBuffer += n
    } else if (!n.isClosed) {
      n match {
        case an: g.AndNode =>
          an.descendents.foreach(findIn)

        case on: g.OrNode =>
          if (on.descendents.nonEmpty) {
            findIn(on.descendents.minBy(_.histogram))
          }
      }
    }
  }

  var counter = 0;
  def findNodeToExpandFrom(from: Node): Option[Node] = {
    counter += 1
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

class ManualSearch(ctx: LeonContext, problem: Problem, costModel: CostModel) extends Search(ctx, problem, costModel) {
  import g.{Node, AndNode, OrNode, RootNode}

  import ctx.reporter._

  var cd       = List[Int]()
  var cmdQueue = List[String]()

  override def doStep(n: Node, sctx: SynthesisContext) = {
    super.doStep(n, sctx);

    // Backtrack view to a point where node is neither closed nor solved
    if (n.isClosed || n.isSolved) {
      var from: Node = g.root
      var newCd = List[Int]()

      while (!from.isSolved && !from.isClosed && newCd.size < cd.size) {
        val cdElem = cd(newCd.size)
        from = traversePathFrom(from, List(cdElem)).get
        if (!from.isSolved && !from.isClosed) {
          newCd = cdElem :: newCd
        }
      }

      cd = newCd.reverse
    }
  }

  def printGraph() {
    def pathToString(path: List[Int]): String = {
      val p = path.reverse.drop(cd.size)
      if (p.isEmpty) {
        ""
      } else {
        " "+p.mkString(" ")
      }
    }

    def title(str: String)  = "\u001b[1m"  + str + "\u001b[0m"
    def failed(str: String) = "\u001b[31m" + str + "\u001b[0m"
    def solved(str: String) = "\u001b[32m" + str + "\u001b[0m"

    def displayHistogram(h: Histogram): String = {
      val (max, maxarg) = h.maxInfo
      f"$max%,2f@$maxarg%2d"
    }

    def displayNode(n: Node): String = n match {
      case an: AndNode =>
        val app = an.ri
        s"(${displayHistogram(n.histogram)}) $app"
      case on: OrNode =>
        val p = on.p
        s"(${displayHistogram(n.histogram)}) $p"
    }

    def traversePathFrom(n: Node, prefix: List[Int]) {
      val visible = (prefix endsWith cd.reverse)

      if (!n.isExpanded) {
        if (visible) {
          println(pathToString(prefix)+" \u2508 "+displayNode(n))
        }
      } else if (n.isSolved) {
        println(solved(pathToString(prefix)+" \u2508 "+displayNode(n)))
      } else if (n.isClosed) {
        println(failed(pathToString(prefix)+" \u2508 "+displayNode(n)))
      } else {
        if (visible) {
          println(title(pathToString(prefix)+" \u2510 "+displayNode(n)))
        }
      }

      if (n.isExpanded && !n.isClosed && !n.isSolved) {
        for ((sn, i) <- n.descendents.zipWithIndex) {
          traversePathFrom(sn, i :: prefix)
        }
      }
    }

    println("-"*80)
    traversePathFrom(g.root, List())
    println("-"*80)
  }

  var continue = true

  def findNodeToExpandFrom(from: Node): Option[Node] = {
    if (!from.isExpanded) {
      Some(from)
    } else {
      var res: Option[Node] = None
      continue = true

      while(continue) {
        printGraph()

        try {
          print("Next action? (q to quit) "+cd.mkString(" ")+" $ ")
          val line = if (cmdQueue.isEmpty) {
            scala.io.StdIn.readLine()
          } else {
            val n = cmdQueue.head
            println(n)
            cmdQueue = cmdQueue.tail
            n
          }
          if (line == "q") {
            continue = false
            res = None
          } else if (line startsWith "cd") {
            val parts = line.split("\\s+").toList

            parts match {
              case List("cd") =>
                cd = List()
              case List("cd", "..") =>
                if (cd.size > 0) {
                  cd = cd.dropRight(1)
                }
              case "cd" :: parts =>
                cd = cd ::: parts.map(_.toInt)
              case _ =>
            }

          } else {
            val parts = line.split("\\s+").toList

            val c = parts.head.toInt
            cmdQueue = cmdQueue ::: parts.tail

            traversePath(cd ::: c :: Nil) match {
              case Some(l) if !l.isExpanded =>
                res = Some(l)
                cd = cd ::: c :: Nil
                continue = false
              case Some(n) =>
                cd = cd ::: c :: Nil
              case None =>
                error("Invalid path")
            }
          }
        } catch {
          case e: java.lang.NumberFormatException =>

          case e: java.io.IOException =>
            continue = false

          case e: Throwable =>
            error("Woops: "+e.getMessage())
            e.printStackTrace()
        }
      }
      res
    }
  }
}
