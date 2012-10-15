import sbt._
import Process._
import Keys._

object Leon extends Build {
  private val scriptName = "leon"
  def scriptFile = file(".") / scriptName
  def is64 = System.getProperty("sun.arch.data.model") == "64"
  def ldLibraryDir32 = file(".") / "lib-bin"
  def ldLibraryDir64 = file(".") / "lib64-bin"

  val scriptTask = TaskKey[Unit]("script", "Generate the " + scriptName + " Bash script") <<= (streams, dependencyClasspath in Compile, classDirectory in Compile) map { (s, deps, out) =>
    if(!scriptFile.exists) {
      s.log.info("Generating script ("+(if(is64) "64b" else "32b")+")...")
      try {
        val depsPaths = deps.map(_.data.absolutePath)

        val depsPaths64 = depsPaths.filterNot(_.endsWith("unmanaged/z3.jar"))
        val depsPaths32 = depsPaths.filterNot(_.endsWith("unmanaged/z3-64.jar"))

        // One ugly hack... Likely to fail for Windows, but it's a Bash script anyway.
        val scalaHomeDir = depsPaths.find(_.endsWith("lib/scala-library.jar")) match {
          case None => throw new Exception("Couldn't guess SCALA_HOME.")
          case Some(p) => p.substring(0, p.length - 21)
        }
        s.log.info("Will use " + scalaHomeDir + " as SCALA_HOME.")

        val nl = System.getProperty("line.separator")
        val fw = new java.io.FileWriter(scriptFile)
        fw.write("#!/bin/bash --posix" + nl)
        if (is64) {
          fw.write("SCALACLASSPATH=\"")
          fw.write((out.absolutePath +: depsPaths64).mkString(":"))
          fw.write("\"" + nl + nl)

          // Setting the dynamic lib path
          fw.write("LIBRARY_PATH=\"" + ldLibraryDir64.absolutePath + "\"" + nl)
        } else {
          fw.write("if [ `uname -m` == \"x86_64\" ]; then "+nl)

            fw.write("SCALACLASSPATH=\"")
            fw.write((out.absolutePath +: depsPaths64).mkString(":"))
            fw.write("\"" + nl + nl)

            // Setting the dynamic lib path
            fw.write("LIBRARY_PATH=\"" + ldLibraryDir64.absolutePath + "\"" + nl)

          fw.write("else" + nl)

            fw.write("SCALACLASSPATH=\"")
            fw.write((out.absolutePath +: depsPaths32).mkString(":"))
            fw.write("\"" + nl + nl)

            // Setting the dynamic lib path
            fw.write("LIBRARY_PATH=\"" + ldLibraryDir32.absolutePath + "\"" + nl)
          fw.write("fi" + nl)

        }

        // the Java command that uses sbt's local Scala to run the whole contraption.
        fw.write("LD_LIBRARY_PATH=\"$LIBRARY_PATH\" \\"+nl)
        fw.write("java -Xmx2G -Xms512M -classpath ${SCALACLASSPATH} -Dscala.home=\"")
        fw.write(scalaHomeDir)
        fw.write("\" -Dscala.usejavacp=true ")
        fw.write("scala.tools.nsc.MainGenericRunner -classpath ${SCALACLASSPATH} ")
        fw.write("leon.Main $@" + nl)
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
  ) aggregate(leonLibrary) dependsOn(leonLibrary) 

  lazy val leonLibrary = Project(id = "leon-library", base = file("./library"))

}
