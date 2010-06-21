import sbt._

class FunCheckProject(info: ProjectInfo) extends DefaultProject(info) with FileTasks {
  override def outputDirectoryName = "bin"
  override def dependencyPath      = "lib"
  override def shouldCheckOutputDirectories = false

  lazy val purescala = project(".", "PureScala Definitions", new PureScalaProject(_))
  lazy val plugin    = project(".", "FunCheck Plugin", new PluginProject(_), purescala)
  lazy val multisets = project(".", "Multiset Solver", new MultisetsProject(_), plugin, purescala)

  val scriptPath: Path = "." / "scalac-funcheck"

  lazy val all = fileTask(scriptPath :: Nil)(generateScript) dependsOn(purescala.`package`, plugin.`package`) describedAs("Compile everything and produce a script file.")

  override def cleanAction = super.cleanAction dependsOn(deleteScript)

  lazy val deletescr = deleteScript

  def deleteScript = task {
    scriptPath.asFile.delete
    None
  }

  def generateScript: Option[String] = {
    try {
      val nl = System.getProperty("line.separator")
      val f = scriptPath.asFile
      val fw = new java.io.FileWriter(f)
      fw.write("#!/bin/sh" + nl)
      fw.write("LD_LIBRARY_PATH=" + ("." / "lib-bin").absolutePath + " \\" + nl)
      fw.write("java \\" + nl)

      // This is a hack :(
      val libStr = (buildLibraryJar.absolutePath).toString
      fw.write("    -Dscala.home=" + libStr.substring(0, libStr.length-21) + " \\" + nl)

      fw.write("    -classpath \\" + nl)
      fw.write("    " + buildLibraryJar.absolutePath + ":")
      fw.write(buildCompilerJar.absolutePath + ":")
      fw.write(purescala.jarPath.absolutePath + ":")
      fw.write(plugin.jarPath.absolutePath + ":")
      fw.write(("lib" / "z3.jar").absolutePath + " \\" + nl)
      fw.write("  scala.tools.nsc.Main -Xplugin:" + plugin.jarPath.absolutePath + " $@" + nl)
      fw.close
      f.setExecutable(true)
      None
    } catch {
      case e => Some("There was an error while generating the script file: " + e.getLocalizedMessage)
    }
  }

  sealed abstract class PersonalizedProject(info: ProjectInfo) extends DefaultProject(info) {
    override def dependencyPath = "lib"
    override def outputDirectoryName = "bin" 
    override def compileOptions = super.compileOptions ++ Seq(Unchecked)
  }  
  class PureScalaProject(info: ProjectInfo) extends PersonalizedProject(info) {
    override def outputPath = "bin" / "purescala"
    override def mainScalaSourcePath = "src" / "purescala"

  }
  class PluginProject(info: ProjectInfo) extends PersonalizedProject(info) {
    override def outputPath = "bin" / "funcheck"
    override def mainScalaSourcePath = "src" / "funcheck"
    override def unmanagedClasspath = super.unmanagedClasspath +++ purescala.jarPath
    override def mainResourcesPath   = "resources" / "funcheck"
  }
  class MultisetsProject(info: ProjectInfo) extends PersonalizedProject(info) {
    override def outputPath = "bin" / "multisets"
    override def mainScalaSourcePath = "src" / "multisets"
    override def unmanagedClasspath = super.unmanagedClasspath +++ purescala.jarPath
  }
}
