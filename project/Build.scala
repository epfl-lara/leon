import sbt._
import Process._
import Keys._

object Leon extends Build {
  private val scriptName = "leon"
  def scriptFile = file(".") / scriptName
  def ldLibraryDir = file(".") / "lib-bin"

  val scriptTask = TaskKey[Unit]("script", "Generate the " + scriptName + " Bash script") <<= (streams, dependencyClasspath in Compile, classDirectory in Compile) map { (s, deps, out) =>
    if(!scriptFile.exists) {
      s.log.info("Generating script...")
      try {
        val depsPaths = deps.map(_.data.absolutePath)
        // One ugly hack... Likely to fail for Windows, but it's a Bash script anyway.
        val scalaHomeDir = depsPaths.find(_.endsWith("lib/scala-library.jar")) match {
          case None => throw new Exception("Couldn't guess SCALA_HOME.")
          case Some(p) => p.substring(0, p.length - 21)
        }
        s.log.info("Will use " + scalaHomeDir + " as SCALA_HOME.")

        val nl = System.getProperty("line.separator")
        val fw = new java.io.FileWriter(scriptFile)
        fw.write("#!/bin/bash --posix" + nl)
        fw.write("SCALACLASSPATH=\"")
        fw.write((out.absolutePath +: depsPaths).mkString(":"))
        fw.write("\"" + nl + nl)

        // Setting the dynamic lib path
        fw.write("LD_LIBRARY_PATH=\"" + ldLibraryDir.absolutePath + "\" \\" + nl)

        // the Java command that uses sbt's local Scala to run the whole contraption.
        fw.write("java -Xmx2G -Xms512M -classpath ${SCALACLASSPATH} -Dscala.home=\"")
        fw.write(scalaHomeDir)
        fw.write("\" -Dscala.usejavacp=true ")
        fw.write("scala.tools.nsc.MainGenericRunner -classpath ${SCALACLASSPATH} ")
        fw.write("leon.plugin.Main $@" + nl)
        fw.close
        scriptFile.setExecutable(true)
      } catch {
        case e => s.log.error("There was an error while generating the script file: " + e.getLocalizedMessage)
      }
    }
  }

  object LeonProject {
    val settings = Seq(
      scriptTask
    )
  }

  lazy val root = Project(
    id = "leon",
    base = file("."),
    settings = Project.defaultSettings ++ LeonProject.settings
  )
}
