import sbt._

class FunCheckProject(info: ProjectInfo) extends ParentProject(info) {
  override def outputDirectoryName = "bin"
  override def dependencyPath      = "lib"
  override def shouldCheckOutputDirectories = false
  lazy val purescala = project(".", "PureScala Definitions", new PureScalaProject(_))
  lazy val plugin    = project(".", "FunCheck Plugin", new PluginProject(_), purescala)
  lazy val multisets = project(".", "Multiset Solver", new MultisetsProject(_), plugin, purescala)

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
