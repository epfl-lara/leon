/* Copyright 2009-2013 EPFL, Lausanne */

package leon
package synthesis

import purescala.Trees._
import purescala.Common.Tree
import purescala.Definitions.FunDef
import purescala.ScalaPrinter

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

        val newCode = ScalaPrinter(toTree, fromTree.getPos.col/2)

        before + newCode + after

      case _ =>
        sys.error("Substitution requires RangePos on the input tree: "+fromTree)
    }
  }

  def readFile(file: File): String = {
    scala.io.Source.fromFile(file).mkString
  }
}
