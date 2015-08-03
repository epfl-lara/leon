/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package utils

import java.io.{File, BufferedWriter, FileWriter}

object TemporaryInputPhase extends LeonPhase[(List[String], List[String]), List[String]] {

  val name = "Temporary Input"
  val description = "Create source files from string content"

  def run(ctx: LeonContext)(data: (List[String], List[String])): List[String] = {
    val (contents, opts) = data

    val files = contents.map { content =>
      val file : File = File.createTempFile("leon", ".scala")
      file.deleteOnExit()
      val out = new BufferedWriter(new FileWriter(file))
      out.write(content)
      out.close()
      file.getAbsolutePath
    }


    files ::: opts
  }
}
