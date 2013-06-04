/* Copyright 2009-2013 EPFL, Lausanne */

package leon

// typically these settings can be changed through some command-line switch.
// TODO this global object needs to die (or at least clean out of its var's)
object Settings {
  lazy val reporter: Reporter = new DefaultReporter

  var showIDs: Boolean = false

  def defaultClassPath() = {
    val leonLib = System.getenv("LEON_LIBRARY_PATH")
    if (leonLib == "" || leonLib == null) {
      sys.error("LEON_LIBRARY_PATH env variable is undefined")
    }

    val leonCPs = leonLib

    val scalaHome = System.getenv("SCALA_HOME")
    val scalaCPs = if (scalaHome != "") {
      val f = new java.io.File(scalaHome+"/lib")

      f.listFiles().collect {
        case f if f.getPath().endsWith(".jar") => f.getAbsolutePath()
      }.toList

    } else {
      Nil
    }

    leonCPs :: scalaCPs
  }
}

case class Settings(
  val strictCompilation: Boolean = true, // Terminates Leon in case an error occured during extraction
  val termination: Boolean       = false,
  val synthesis: Boolean         = false,
  val xlang: Boolean             = false,
  val verify: Boolean            = true,
  // This is a list of directories that is passed as class-path of the inner-compiler.
  // It needs to contain at least a directory containing scala-library.jar, and
  // one for the leon runtime library.
  val classPath: List[String]    = Settings.defaultClassPath()
)
