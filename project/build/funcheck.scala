import sbt._

class FunCheckProject(info: ProjectInfo) extends DefaultProject(info) {
  override def outputDirectoryName = "bin"
  override def mainScalaSourcePath = "src"
  override def mainResourcesPath   = "resources"
  override def dependencyPath      = "lib"

  override def compileOptions = super.compileOptions ++ Seq(Unchecked)

  lazy val scalac = task {
    println("Running scalac...")
    None
  } dependsOn(`package`) describedAs("Runs scalac with the FunCheck plugin.")
}
