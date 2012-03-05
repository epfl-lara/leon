package leon

// typically these settings can be changed through some command-line switch.
object Settings {
  var experimental : Boolean = false
  var showIDs: Boolean = false
  var functionsToAnalyse: Set[String] = Set.empty
  var extensionNames: Seq[String] = Nil
  lazy val reporter: Reporter = new DefaultReporter
  var runDefaultExtensions: Boolean = true
  var noForallAxioms: Boolean = true
  var unrollingLevel: Int = 0
  var zeroInlining : Boolean = true
  var useBAPA: Boolean = false
  var impureTestcases: Boolean = false
  var nbTestcases: Int = 1
  var testBounds: (Int, Int) = (0, 3)
  var useCores : Boolean = false
  var pruneBranches : Boolean = false
  var solverTimeout : Option[Int] = None
  var luckyTest : Boolean = true
  var useQuickCheck : Boolean = false
  var useParallel : Boolean = false
  // When this is None, use real integers
  var bitvectorBitwidth : Option[Int] = None
  var useTemplates : Boolean = false
}
