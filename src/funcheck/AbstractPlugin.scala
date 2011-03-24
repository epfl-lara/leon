package funcheck

import scala.tools.nsc
import scala.tools.nsc.{Global,Phase}
import scala.tools.nsc.plugins.{Plugin,PluginComponent}

abstract class AbstractPlugin extends Plugin {
  import global._

  var silentlyTolerateNonPureBodies: Boolean = false
}
