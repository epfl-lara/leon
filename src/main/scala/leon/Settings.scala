package leon

// typically these settings can be changed through some command-line switch.
// TODO this global object needs to die (or at least clean out of its var's)
object Settings {
  lazy val reporter: Reporter = new DefaultReporter

  var showIDs: Boolean = false
  var silentlyTolerateNonPureBodies: Boolean = false

  def defaultClassPath() = {
    val env = System.getenv("SCALA_HOME")
    if (env != "") {
      List(env+"/lib")
    } else {
      Nil
    }
  }
}

case class Settings(
  val synthesis: Boolean      = false,
  val xlang: Boolean          = false,
  val verify: Boolean         = true,
  // This is a list of directories that is passed as class-path of the inner-compiler.
  // It needs to contain at least a directory containing scala-library.jar, and
  // one for the leon runtime library.
  val classPath: List[String] = Settings.defaultClassPath()
)
