package leon

// typically these settings can be changed through some command-line switch.
// TODO this global object needs to die (or at least clean out of its var's)
object Settings {
  var showIDs: Boolean = false
  lazy val reporter: Reporter = new DefaultReporter
  var useBAPA: Boolean = false
  var impureTestcases: Boolean = false
  var nbTestcases: Int = 1
  var testBounds: (Int, Int) = (0, 3)
  var solverTimeout : Option[Int] = None
  var useQuickCheck : Boolean = false
  var useParallel : Boolean = false
  var debugLevel: Int = 0
  var synthesis: Boolean = false
  var transformProgram: Boolean              = true
  var stopAfterExtraction: Boolean           = false
  var stopAfterTransformation: Boolean       = false
  var stopAfterAnalysis: Boolean             = true
  var silentlyTolerateNonPureBodies: Boolean = false
}

case class Settings(
  val synthesis: Boolean    = false,
  val xlang: Boolean        = false,
  val verify: Boolean       = true
)
