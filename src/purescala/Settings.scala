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
  var useInstantiator: Boolean = false
}
