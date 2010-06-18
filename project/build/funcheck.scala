import sbt._

class FunCheckProject(info: ProjectInfo) extends DefaultProject(info) {
  override def outputDirectoryName = "bin"
  override def mainScalaSourcePath = "src"
  override def compileOptions = super.compileOptions ++ Seq(Unchecked)
}
