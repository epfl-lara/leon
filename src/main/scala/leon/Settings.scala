/* Copyright 2009-2014 EPFL, Lausanne */

package leon

import utils.DebugSection

case class Settings(
  val strictCompilation: Boolean       = true, // Terminates Leon in case an error occured during extraction
  val debugSections: Set[DebugSection] = Set(), // Enables debug message for the following sections
  val termination: Boolean             = false,
  val synthesis: Boolean               = false,
  val xlang: Boolean                   = false,
  val verify: Boolean                  = true,
  val injectLibrary: Boolean           = false,
  val classPath: List[String]          = Settings.defaultClassPath()
)

object Settings {
  // This is a list of directories that is passed as class-path of the inner-compiler.
  // It needs to contain at least a directory containing scala-library.jar, and
  // one for the leon runtime library.

  private def defaultClassPath() = {
    val scalaHome = System.getenv("SCALA_HOME")
    assert(scalaHome ne null, "SCALA_HOME was not found in the environment, did you run `source setupenv.sh` ?")

    if (scalaHome != "") {
      val f = new java.io.File(scalaHome+"/lib")

      f.listFiles().collect {
        case f if f.getPath().endsWith(".jar") => f.getAbsolutePath()
      }.toList

    } else {
      Nil
    }
  }

  private[leon] def defaultLibFiles() = {
    Option(System.getenv("LEON_LIBFILES")).map(_.split(" ").toList).getOrElse(Nil)
  }

}
