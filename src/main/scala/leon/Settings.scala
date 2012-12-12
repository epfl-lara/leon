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
  val classPath: List[String] = Settings.defaultClassPath()
)
