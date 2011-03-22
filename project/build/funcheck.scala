import sbt._

class FunCheckProject(info: ProjectInfo) extends DefaultProject(info) with FileTasks {
  val scalatest = "org.scalatest" % "scalatest" % "1.2"

  override def outputDirectoryName = "bin"
  override def dependencyPath      = "lib"
  override def shouldCheckOutputDirectories = false

  lazy val purescala      = project(".", "PureScala Definitions", new PureScalaProject(_))
  lazy val plugin         = project(".", "FunCheck Plugin", new PluginProject(_), purescala, multisetsLib)
  lazy val multisetsLib   = project(".", "Multiset Placeholder Library", new MultisetsLibProject(_))
  lazy val multisets      = project(".", "Multiset Solver", new MultisetsProject(_), plugin, purescala, multisetsLib)
  lazy val orderedsets    = project(".", "Ordered Sets Solver", new OrderedSetsProject(_), plugin, purescala)
  lazy val setconstraints = project(".", "Type inference with set constraints", new SetConstraintsProject(_), plugin, purescala)

  lazy val extensionJars : List[Path] = multisetsLib.jarPath :: multisets.jarPath :: orderedsets.jarPath :: setconstraints.jarPath :: Nil

  val scriptPath: Path = "." / "scalac-funcheck"

  lazy val all = task { None } dependsOn(generateScript) describedAs("Compile everything and produce a script file.")

  override def cleanAction = super.cleanAction dependsOn(cleanScript)

  lazy val generateScript = genScript
  def genScript = fileTask(scriptPath ::Nil)({
    log.info("Generating runner script")
    try {
      val nl = System.getProperty("line.separator")
      val f = scriptPath.asFile
      val fw = new java.io.FileWriter(f)
      fw.write("#!/bin/bash" + nl)
      fw.write("FUNCHECKCLASSPATH=\"")
      fw.write(buildLibraryJar.absolutePath + ":")
      fw.write(buildCompilerJar.absolutePath + ":")
      fw.write(purescala.jarPath.absolutePath + ":")
      fw.write(plugin.jarPath.absolutePath + ":")
      fw.write(("lib" / "z3.jar").absolutePath)
      fw.write("\"" + nl + nl)
      fw.write("for f in " + extensionJars.map(_.absolutePath).map(n => "\"" + n + "\"").mkString(" ") + "; do" + nl)
      fw.write("  if [ -e ${f} ]" + nl)
      fw.write("  then" + nl)
      fw.write("    FUNCHECKCLASSPATH=${FUNCHECKCLASSPATH}:${f}" + nl)
      fw.write("  fi" + nl)
      fw.write("done" + nl + nl)
      fw.write("SCALACCLASSPATH=\"")
      fw.write(multisetsLib.jarPath.absolutePath + ":")
      fw.write(plugin.jarPath.absolutePath + ":")
      fw.write(purescala.jarPath.absolutePath)
      fw.write("\"" + nl + nl)
      fw.write("LD_LIBRARY_PATH=" + ("." / "lib-bin").absolutePath + " \\" + nl)
      fw.write("java -Xmx1024M \\" + nl)

      // This is a hack :(
      val libStr = (buildLibraryJar.absolutePath).toString
      fw.write("    -Dscala.home=" + libStr.substring(0, libStr.length-21) + " \\" + nl)

      fw.write("    -classpath ${FUNCHECKCLASSPATH} \\" + nl)
      fw.write("  scala.tools.nsc.Main -Xplugin:" + plugin.jarPath.absolutePath + " -classpath ${SCALACCLASSPATH} $@" + nl)
      fw.close
      f.setExecutable(true)
      None
    } catch {
      case e => Some("There was an error while generating the script file: " + e.getLocalizedMessage)
    }
  }) dependsOn(plugin.`package`) describedAs("Produce the runner script.")

  lazy val cleanScript = clnScript
  def clnScript = task {
    log.info("Deleting runner script")
    scriptPath.asFile.delete
    None
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
    override def unmanagedClasspath = super.unmanagedClasspath +++ purescala.jarPath +++ multisetsLib.jarPath
    override def mainResourcesPath   = "resources" / "funcheck"
  }
  class MultisetsLibProject(info: ProjectInfo) extends PersonalizedProject(info) {
    override def outputPath = "bin" / "multisets-lib"
    override def mainScalaSourcePath = "src" / "multisets-lib"
    override def unmanagedClasspath = super.unmanagedClasspath 
  }
  class MultisetsProject(info: ProjectInfo) extends PersonalizedProject(info) {
    override def outputPath = "bin" / "multisets"
    override def mainScalaSourcePath = "src" / "multisets"
    override def unmanagedClasspath = super.unmanagedClasspath +++ purescala.jarPath
  }
  class OrderedSetsProject(info: ProjectInfo) extends PersonalizedProject(info) {
    override def outputPath = "bin" / "orderedsets"
    override def mainScalaSourcePath = "src" / "orderedsets"
    override def unmanagedClasspath = super.unmanagedClasspath +++ purescala.jarPath
  }
  class SetConstraintsProject(info: ProjectInfo) extends PersonalizedProject(info) {
    override def outputPath = "bin" / "setconstraints"
    override def mainScalaSourcePath = "src" / "setconstraints"
    override def testScalaSourcePath = "src" / "setconstraints-tests"
    override def unmanagedClasspath = super.unmanagedClasspath +++ purescala.jarPath
  }
}
