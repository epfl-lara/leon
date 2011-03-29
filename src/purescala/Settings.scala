package purescala

// typically these settings can be changed through some command-line switch.
object Settings {
  var experimental : Boolean = false
  var showIDs: Boolean = false
  var quietExtensions: Boolean = false
  var functionsToAnalyse: Set[String] = Set.empty
  var extensionNames: Seq[String] = Nil
  var reporter: Reporter = new DefaultReporter
  var quietReporter: Reporter = new QuietReporter
  var runDefaultExtensions: Boolean = true
  var noForallAxioms: Boolean = true
  var unrollingLevel: Int = 0
  var zeroInlining : Boolean = false
  var useBAPA: Boolean = true
  var impureTestcases: Boolean = false
  var nbTestcases: Int = 1
  var testBounds: (Int, Int) = (0, 3)
  var useInstantiator: Boolean = false
  var useFairInstantiator: Boolean = false
  var useCores : Boolean = false
  var pruneBranches : Boolean = false
  def useAnyInstantiator : Boolean = useInstantiator || useFairInstantiator
  var solverTimeout : Option[Int] = None
}
