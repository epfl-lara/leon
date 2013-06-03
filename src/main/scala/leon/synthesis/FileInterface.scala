/* Copyright 2009-2013 EPFL, Lausanne */

package leon
package synthesis

import purescala.Trees._
import purescala.ScalaPrinter

import java.io.File
class FileInterface(reporter: Reporter) {

  def updateFile(origFile: File, solutions: Map[ChooseInfo, Expr], ignoreMissing: Boolean = false) {
    import java.io.{File, BufferedWriter, FileWriter}
    val FileExt = """^(.+)\.([^.]+)$""".r

    origFile.getAbsolutePath() match {
      case FileExt(path, "scala") =>
        var i = 0
        def savePath = path+".scala."+i
        while (new File(savePath).isFile()) {
          i += 1
        }

        val origCode = readFile(origFile)
        val backup   = new File(savePath)
        val newFile  = new File(origFile.getAbsolutePath())
        origFile.renameTo(backup)


        val newCode = substitueChooses(origCode, solutions, ignoreMissing)

        val out = new BufferedWriter(new FileWriter(newFile))
        out.write(newCode)
        out.close
      case _ =>

    }
  }

  def substitueChooses(str: String, solutions: Map[ChooseInfo, Expr], ignoreMissing: Boolean = false): String = {
    var lines = List[Int]()

    // Compute line positions
    var lastFound = -1
    do {
      lastFound = str.indexOf('\n', lastFound+1)

      if (lastFound > -1) {
        lines = lastFound :: lines
      }
    } while(lastFound> 0)
    lines = lines.reverse;

    def lineOf(offset: Int): (Int, Int) = {
      lines.zipWithIndex.find(_._1 > offset) match {
        case Some((off, no)) =>
          (no+1, if (no > 0) lines(no-1) else 0)
        case None =>
          (lines.size+1, lines.lastOption.getOrElse(0))
      }
    }

    def getLineIndentation(offset: Int): Int = {
      var i = str.lastIndexOf('\n', offset)+1

      var res = 0;

      while (i < str.length) {
        val c = str.charAt(i)
        i += 1

        if (c == ' ') {
          res += 1
        } else if (c == '\t') {
          res += 4
        } else {
          i = str.length
        }
      }

      res
    }

    lastFound = -1

    var newStr = str
    var newStrOffset = 0

    do {
      lastFound = str.indexOf("choose", lastFound+1)

      if (lastFound > -1) {
        val (lineno, lineoffset) = lineOf(lastFound)
        // compute scala equivalent of the position:
        val scalaOffset = str.substring(lineoffset, lastFound).replaceAll("\t", " "*8).length

        val indent = getLineIndentation(lastFound)

        solutions.find(_._1.ch.posIntInfo == (lineno, scalaOffset)) match {
          case Some((choose, solution)) =>
            var lvl      = 0;
            var i        = lastFound + 6;
            var continue = true;
            do {
              val c = str.charAt(i)
              if (c == '(' || c == '{') {
                lvl += 1
              } else if (c == ')' || c == '}') {
                lvl -= 1
                if (lvl == 0) {
                  continue = false
                }
              }
              i += 1
            } while(continue)

            val newCode = ScalaPrinter(solution, indent/2)
            newStr = (newStr.substring(0, lastFound+newStrOffset))+newCode+(newStr.substring(i+newStrOffset, newStr.length))

            newStrOffset += -(i-lastFound)+newCode.length

          case _ =>
            if (!ignoreMissing) {
              reporter.warning("Could not find solution corresponding to choose at "+lineno+":"+scalaOffset)
            }
        }
      }
    } while(lastFound> 0)

    newStr
  }

  def readFile(file: File): String = {
    scala.io.Source.fromFile(file).mkString
  }
}
