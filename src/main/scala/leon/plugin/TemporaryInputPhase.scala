/* Copyright 2009-2013 EPFL, Lausanne */

package leon
package plugin

import java.io.{File, BufferedWriter, FileWriter}

object TemporaryInputPhase extends LeonPhase[(String, List[String]), List[String]] {

  val name = "Temporary Input"
  val description = "Feed the compiler with a temporary input file"

  def run(ctx: LeonContext)(data: (String, List[String])): List[String] = {
    val (content, opts) = data

    val file : File = File.createTempFile("leon", ".scala")
    file.deleteOnExit
    val out = new BufferedWriter(new FileWriter(file))
    out.write(content)
    out.close

    file.getAbsolutePath() :: opts
  }
}
