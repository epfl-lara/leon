package funcheck

object DefaultMain {
  def main(args: Array[String]): Unit = {
    println("Please use funCheck as a scalac plugin, running:")
    println("  scalac -Xplugin:funcheck-plugin.jar ...")
  }
}
