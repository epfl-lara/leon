import sbt._
import Process._
import Keys._

object Leon extends Build {
  private val scriptName = "leon"
  private val setupScriptName = "setupenv"

  def scriptFile      = file(".") / scriptName
  def setupScriptFile = file(".") / setupScriptName

  def is64 = System.getProperty("sun.arch.data.model") == "64"
  def ldLibraryDir32 = file(".") / "lib-bin" / "32"
  def ldLibraryDir64 = file(".") / "lib-bin" / "64"

  val cleanTask = TaskKey[Unit]("clean", "Cleans up the generated binaries and scripts.") <<= (streams, clean) map { (s,c) =>
    c
    if(scriptFile.exists && scriptFile.isFile) {
      scriptFile.delete
    }
  }

  val scriptTask = TaskKey[Unit]("script", "Generate the " + scriptName + " and " + setupScriptName + " Bash scriptes") <<= (streams, dependencyClasspath in Compile, classDirectory in Compile) map { (s, deps, out) =>
    if(scriptFile.exists) {
      s.log.info("Re-generating script ("+(if(is64) "64b" else "32b")+")...")
      scriptFile.delete
    } else {
      s.log.info("Generating script ("+(if(is64) "64b" else "32b")+")...")
    }
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
      val ldLibPath = if (is64) {
        fw.write("SCALACLASSPATH=\"")
        fw.write((out.absolutePath +: depsPaths).mkString(":"))
        fw.write("\"" + nl + nl)

        // Setting the dynamic lib path
        ldLibraryDir64.absolutePath
      } else {
        fw.write("if [ `uname -m` == \"x86_64\" ]; then "+nl)

          fw.write("    echo \"It appears you have compiled Leon with a 32bit virtual machine, but are now trying to run it on a 64bit architecture. This is unfortunately not supported.\"" + nl)
          fw.write("    exit -1" + nl)

        fw.write("else" + nl)

          fw.write("    SCALACLASSPATH=\"")
          fw.write((out.absolutePath +: depsPaths).mkString(":"))
          fw.write("\"" + nl)

          // Setting the dynamic lib path
        fw.write("fi" + nl + nl)

        ldLibraryDir32.absolutePath
      }

      val leonLibPath = depsPaths.find(_.endsWith("/library/target/scala-2.9.2/classes")) match {
        case None => throw new Exception("Couldn't find leon-library in the classpath.")
        case Some(p) => p
      }

      fw.write("source "+setupScriptFile.getAbsolutePath()+nl)
      // the Java command that uses sbt's local Scala to run the whole contraption.
      fw.write("java -Xmx2G -Xms512M -classpath ${SCALACLASSPATH} -Dscala.home=\"")
      fw.write(scalaHomeDir)
      fw.write("\" -Dscala.usejavacp=true ")
      fw.write("scala.tools.nsc.MainGenericRunner -classpath ${SCALACLASSPATH} ")
      fw.write("leon.Main $@" + nl)
      fw.close
      scriptFile.setExecutable(true)

      s.log.info("Generating setup script ("+(if(is64) "64b" else "32b")+")...")
      val sfw = new java.io.FileWriter(setupScriptFile)
      sfw.write("#!/bin/bash --posix" + nl)
      sfw.write("export LD_LIBRARY_PATH=\""+ldLibPath+"\"" + nl)
      sfw.write("export LEON_LIBRARY_PATH=\""+leonLibPath+"\"" + nl)
      sfw.write("export SCALA_HOME=\""+scalaHomeDir+"\"" + nl)
      sfw.close
      setupScriptFile.setExecutable(true)

    } catch {
      case e => s.log.error("There was an error while generating the script file: " + e.getLocalizedMessage)
    }
  }

  object LeonProject {
    val settings = Seq(
      scriptTask,
      cleanTask
    )
  }

  lazy val root = Project(
    id = "leon",
    base = file("."),
    settings = Project.defaultSettings ++ LeonProject.settings
  ) aggregate(leonLibrary) dependsOn(leonLibrary) 

  lazy val leonLibrary = Project(id = "leon-library", base = file("./library"))

}
