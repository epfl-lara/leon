package leon

object Logger {

  //the debug level to display, from 0 (no debug information) to 5 (very verbose)
  //var level = 0

  //each debug information is tagged by a string, the tag variable only display the message with a tag in this set
  //if the set is empty then all tags are displayed
  //var tags: Set[String] = Set()

  val defaultTag = "main"

  private def output(msg: String, lvl: Int, tag: String) {
    if(lvl <= Settings.debugLevel) {
      if(Settings.debugTags.isEmpty || Settings.debugTags.contains(tag)) {
        println("DEBUG: [" + tag + "] " + msg)
      }
    }
  }

  def debug(msg: String, lvl: Int, tag: String = defaultTag) = output(msg, lvl, tag)

}
