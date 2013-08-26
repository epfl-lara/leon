/* Copyright 2009-2013 EPFL, Lausanne */

package leon
package synthesis

import leon.purescala.ScalaPrinter

class ManualSearch(synth: Synthesizer,
                   problem: Problem,
                   rules: Seq[Rule],
                   costModel: CostModel) extends SimpleSearch(synth, problem, rules, costModel) {

  def this(synth: Synthesizer, problem: Problem) = {
    this(synth, problem, synth.rules, synth.options.costModel)
  }

  import synth.reporter._

  var cd       = List[Int]()
  var cmdQueue = List[String]()

  def printGraph() {
    def pathToString(path: List[Int]): String = {
      val p = path.reverse.drop(cd.size)
      if (p.isEmpty) {
        ""
      } else {
        " "+p.mkString(" ")
      }
    }

    def title(str: String) = "\033[1m"+str+"\033[0m"
    def failed(str: String) = "\033[31m"+str+"\033[0m"
    def solved(str: String) = "\033[32m"+str+"\033[0m"

    def traversePathFrom(n: g.Tree, prefix: List[Int]) {
      n match {
        case l: g.AndLeaf =>
          if (prefix.endsWith(cd.reverse)) {
            println(pathToString(prefix)+" \u2508 "+l.task.app)
          }
        case l: g.OrLeaf =>
          if (prefix.endsWith(cd.reverse)) {
            println(pathToString(prefix)+" \u2508 "+l.task.p)
          }
        case an: g.AndNode =>
          if (an.isSolved) {
            if (prefix.endsWith(cd.reverse)) {
              println(solved(pathToString(prefix)+" \u2508 "+an.task.app))
            }
          } else {
            if (prefix.endsWith(cd.reverse)) {
              println(title(pathToString(prefix)+" \u2510 "+an.task.app))
            }
            for ((st, i) <- an.subTasks.zipWithIndex) {
              traversePathFrom(an.subProblems(st), i :: prefix)
            }
          }

        case on: g.OrNode =>
          if (on.isSolved) {
            if (prefix.endsWith(cd.reverse)) {
              println(solved(pathToString(prefix)+on.task.p))
            }
          } else {
            if (prefix.endsWith(cd.reverse)) {
              println(title(pathToString(prefix)+" \u2510 "+on.task.p))
            }
            for ((at, i) <- on.altTasks.zipWithIndex) {
              if (on.triedAlternatives contains at) {
                if (prefix.endsWith(cd.reverse)) {
                  println(failed(pathToString(i :: prefix)+" \u2508 "+at.app))
                }
              } else {
                traversePathFrom(on.alternatives(at), i :: prefix)
              }
            }
          }
      }
    }

    println("-"*80)
    traversePathFrom(g.tree, List())
    println("-"*80)
  }

  override def stop() {
    super.stop()
    cmdQueue = "q" :: Nil
    continue = false
  }

  var continue = true


  override def nextLeaf(): Option[g.Leaf] = {
    g.tree match {
      case l: g.Leaf =>
        Some(l)
      case _ =>

        var res: Option[g.Leaf] = None
        continue = true

        while(continue) {
          printGraph()

          try {

            print("Next action? (q to quit) "+cd.mkString(" ")+" $ ")
            val line = if (cmdQueue.isEmpty) {
              readLine()
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

            } else if (line startsWith "p") {
              val parts = line.split("\\s+").toList.tail.map(_.toInt)
              traversePath(cd ::: parts) match {
                case Some(n) =>
                  println("#"*80)
                  println("AT:"+n.task)
                  val sp = programAt(n)
                  sp.acc.foreach(fd => println(ScalaPrinter(fd)))
                  println("$"*20)
                  println("ROOT: "+sp.fd.id)
                case _ =>
              }

            } else {
              val parts = line.split("\\s+").toList

              val c = parts.head.toInt
              cmdQueue = cmdQueue ::: parts.tail

              traversePath(cd ::: c :: Nil) match {
                case Some(l: g.Leaf) =>
                  res = Some(l)
                  cd = cd ::: c :: Nil
                  continue = false
                case Some(_) =>
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

  override def searchStep() {
    super.searchStep()

    var continue = cd.size > 0
    while(continue) {
      traversePath(cd) match {
        case Some(t) if !t.isSolved =>
          continue = false
        case Some(t) =>
          cd = cd.dropRight(1)
        case None =>
          cd = cd.dropRight(1)
      }
      continue = continue && (cd.size > 0)
    }
  }

}
