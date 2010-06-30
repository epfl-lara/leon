package purescala

// typically these settings can be changed through some command-line switch.
object Settings {
  var showIDs: Boolean = false
  var quietExtensions: Boolean = false
  var extensionNames: String = ""
  var reporter: Reporter = new DefaultReporter
  var quietReporter: Reporter = new QuietReporter
  var runDefaultExtensions: Boolean = true
}
