package leon

// typically these settings can be changed through some command-line switch.
// TODO this global object needs to die (or at least clean out of its var's)
object Settings {
  lazy val reporter: Reporter = new DefaultReporter

  var showIDs: Boolean = false
  var silentlyTolerateNonPureBodies: Boolean = false
}

case class Settings(
  val synthesis: Boolean    = false,
  val xlang: Boolean        = false,
  val verify: Boolean       = true,
  val classPath: String     = 
    List(
      "/home/ekneuss/scala/scala-2.9.2/lib/",
      "/home/ekneuss/git/leon-2.0/library/target/scala-2.9.2/"
    ).mkString(":")
)
