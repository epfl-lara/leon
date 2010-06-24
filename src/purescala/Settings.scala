package purescala

// typically these settings can be changed through some command-line switch.
object Settings {
  var showIDs: Boolean = false
  var extensionNames: String = ""
  var reporter: Reporter = DefaultReporter
  var runDefaultExtensions: Boolean = true
}
