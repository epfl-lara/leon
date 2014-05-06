/* Copyright 2009-2014 EPFL, Lausanne */

package leon
package synthesis

import purescala.Trees._
import purescala.Common.Tree
import purescala.Definitions.FunDef
import purescala.ScalaPrinter
import purescala.PrinterOptions
import purescala.PrinterContext

import leon.utils.RangePosition

import java.io.File
class FileInterface(reporter: Reporter) {

  def updateFile(origFile: File, solutions: Map[ChooseInfo, Expr]) {
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

        var newCode = origCode
        for ( (ci, e) <- solutions) {
          newCode = substitute(newCode, ci.ch, e)
        }

        val out = new BufferedWriter(new FileWriter(newFile))
        out.write(newCode)
        out.close
      case _ =>

    }
  }

  def substitute(str: String, fromTree: Tree, toTree: Tree): String = {

    fromTree.getPos match {
      case rp: RangePosition =>
        val from = rp.pointFrom
        val to   = rp.pointTo

        val before = str.substring(0, from)
        val after  = str.substring(to, str.length)

        // Get base indentation of last line:
        val lineChars = before.substring(before.lastIndexOf('\n')+1).toList

        val indent = lineChars.takeWhile(_ == ' ').size

        val p = new ScalaPrinter(PrinterOptions())
        p.pp(toTree)(PrinterContext(toTree, Some(fromTree), indent/2, p))

        before + "{" + p.toString + "}" + after

      case p =>
        sys.error("Substitution requires RangePos on the input tree: "+fromTree +": "+fromTree.getClass+" GOT" +p)
    }
  }

  def readFile(file: File): String = {
    scala.io.Source.fromFile(file).mkString
  }
}
