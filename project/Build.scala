import sbt._
import Process._
import Keys._

object Leon extends Build {
  private val scriptName      = "leon"
  private val setupScriptName = "setupenv"
  private val benchScriptName = "leon-bench"

  def scriptFile      = file(".") / scriptName
  def benchScriptFile = file(".") / benchScriptName
  def setupScriptFile = file(".") / setupScriptName

  def is64 = System.getProperty("sun.arch.data.model") == "64"
  def ldLibraryDir32 = file(".") / "lib-bin" / "32"
  def ldLibraryDir64 = file(".") / "lib-bin" / "64"

  val cleanTask = TaskKey[Unit]("clean", "Cleans up the generated binaries and scripts.") <<= (streams, clean) map { (s,c) =>
    c
    if(scriptFile.exists && scriptFile.isFile) {
      scriptFile.delete
    }
    if(setupScriptFile.exists && setupScriptFile.isFile) {
      setupScriptFile.delete
    }
    if(benchScriptFile.exists && benchScriptFile.isFile) {
      benchScriptFile.delete
    }
  }

  val nl = System.getProperty("line.separator")

  val setupScriptTask = TaskKey[Seq[String]]("setup", "Generate the " + setupScriptName + "  Bash script")

  val setupSetting = setupScriptTask <<= (streams, dependencyClasspath in Compile, classDirectory in Compile) map { (s, deps, out) =>

    val depsPaths = deps.map(_.data.absolutePath)

    val scalaHomeDir = depsPaths.find(_.endsWith("lib/scala-library.jar")) match {
      case None => throw new Exception("Couldn't guess SCALA_HOME.")
      case Some(p) => p.substring(0, p.length - 21)
    }

    val ldLibPath = if (is64) ldLibraryDir64.absolutePath else ldLibraryDir32.absolutePath

    val leonLibPath = depsPaths.find(_.endsWith("/library/target/scala-2.10/classes")) match {
      case None => throw new Exception("Couldn't find leon-library in the classpath.")
      case Some(p) => p
    }

    // One ugly hack... Likely to fail for Windows, but it's a Bash script anyway.
    s.log.info("Will use " + scalaHomeDir + " as SCALA_HOME.")

    if (setupScriptFile.exists) {
      s.log.info("Regenerating '"+setupScriptFile.getName+"' script ("+(if(is64) "64b" else "32b")+")...")
      setupScriptFile.delete
    } else {
      s.log.info("Generating '"+setupScriptFile.getName+"' script ("+(if(is64) "64b" else "32b")+")...")
    }
    val sfw = new java.io.FileWriter(setupScriptFile)
    sfw.write("#!/bin/bash --posix" + nl)
    if (!is64) {
      sfw.write("if [ `uname -m` == \"x86_64\" ]; then "+nl)
      sfw.write("    echo \"It appears you have compiled Leon with a 32bit virtual machine, but are now trying to run it on a 64bit architecture. This is unfortunately not supported.\"" + nl)
      sfw.write("    exit -1" + nl)
      sfw.write("fi"+ nl)
    }
    sfw.write("export LD_LIBRARY_PATH=\""+ldLibPath+"\"" + nl)
    sfw.write("export LEON_LIBRARY_PATH=\""+leonLibPath+"\"" + nl)
    sfw.write("export SCALA_HOME=\""+scalaHomeDir+"\"" + nl)
    sfw.close
    setupScriptFile.setExecutable(true)

    (out.absolutePath +: depsPaths)
  }

  def genRunnerTask(taskName: String, file: File, name: String, mainClass: String) = {
    TaskKey[Unit](taskName, "Generate the " + name + " Bash script") <<= (streams, setupScriptTask, resourceDirectory in Compile) map { (s, cps, res) =>
      try {
        // Paths discovery
        if(file.exists) {
          s.log.info("Regenerating '"+file.getName+"' script ("+(if(is64) "64b" else "32b")+")...")
          file.delete
        } else {
          s.log.info("Generating '"+file.getName+"' script ("+(if(is64) "64b" else "32b")+")...")
        }

        val fw = new java.io.FileWriter(file)
        fw.write("#!/bin/bash --posix" + nl)

        fw.write("SCALACLASSPATH=\"")
        fw.write((res.getAbsolutePath +: cps).mkString(":"))
        fw.write("\"" + nl + nl)

        fw.write("source "+setupScriptFile.getAbsolutePath()+nl)
        // the Java command that uses sbt's local Scala to run the whole contraption.
        fw.write("java -Xmx2G -Xms512M -classpath ${SCALACLASSPATH} -Dscala.home=\"$SCALA_HOME\" -Dscala.usejavacp=true ")
        fw.write("scala.tools.nsc.MainGenericRunner -classpath ${SCALACLASSPATH} ")
        fw.write(mainClass+" $@" + nl)
        fw.close
        file.setExecutable(true)
      } catch {
        case e => s.log.error("There was an error while generating the script file: " + e.getLocalizedMessage)
      }
    }
  }

  val scriptTask = genRunnerTask("script", scriptFile, scriptName, "leon.Main")
  val benchTask  = genRunnerTask("bench",  benchScriptFile, benchScriptName, "leon.synthesis.utils.Benchmarks")

  object LeonProject {
    val settings = Seq(
      setupSetting,
      scriptTask,
      benchTask,
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
