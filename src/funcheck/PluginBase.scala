package funcheck

import scala.tools.nsc
import scala.tools.nsc.{Global,Phase}
import scala.tools.nsc.plugins.{Plugin,PluginComponent}

abstract class PluginBase extends Plugin {
  import global._

  var silentlyTolerateNonPureBodies: Boolean = false
}
