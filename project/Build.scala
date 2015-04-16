import sbt._
import Process._
import Keys._

object Leon extends Build {
  private val scriptName      = "leon"

  def scriptFile      = file(".") / scriptName

  def is64 = System.getProperty("sun.arch.data.model") == "64"
  def ldLibraryDir32 = file(".") / "lib-bin" / "32"
  def ldLibraryDir64 = file(".") / "lib-bin" / "64"

  val cleanTask = TaskKey[Unit]("clean", "Cleans up the generated binaries and scripts.") <<= (streams, clean) map { (s,c) =>
    if(scriptFile.exists && scriptFile.isFile) {
      scriptFile.delete
    }
  }

  val nl = System.getProperty("line.separator")

  val scriptTask = TaskKey[Unit]("script", "Generate the leon Bash script") <<= (streams, dependencyClasspath in Compile, classDirectory in Compile, resourceDirectory in Compile) map { (s, cps, out, res) =>
    try {
      val f = file("leon")
      // Paths discovery
      if(f.exists) {
        s.log.info("Regenerating '"+f.getName+"' script ("+(if(is64) "64b" else "32b")+")...")
        f.delete
      } else {
        s.log.info("Generating '"+f.getName+"' script ("+(if(is64) "64b" else "32b")+")...")
      }

      val paths = (res.getAbsolutePath +: out.getAbsolutePath +: cps.map(_.data.absolutePath)).mkString(":")

      IO.write(f, s"""|#!/bin/bash --posix
                      |
                      |SCALACLASSPATH="$paths"
                      |
                      |java -Xmx2G -Xms512M -classpath $${SCALACLASSPATH} -Dscala.usejavacp=false scala.tools.nsc.MainGenericRunner -classpath $${SCALACLASSPATH} leon.Main $$@ 2>&1 | tee -i last.log
                      |""".stripMargin)

      f.setExecutable(true)
    } catch {
      case e: Throwable =>
        s.log.error("There was an error while generating the script file: " + e.getLocalizedMessage)
    }
  }

  val sourceGen = {
    sourceGenerators in Compile += Def.task {
      val libFiles = ((baseDirectory.value / "library") ** "*.scala").getPaths.mkString("List(\"", "\", \"", "\")")

      val build = (sourceManaged in Compile).value / "leon" / "Build.scala";

      IO.write(build, s"""|package leon;
                          |
                          |object Build {
                          |val libFiles = $libFiles;
                          |}""".stripMargin)

      Seq(build)
    }.taskValue
  }

  object LeonProject {
    val settings = Seq(
      scriptTask,
      cleanTask,
      sourceGen
    )
  }

  lazy val root = Project(
    id = "leon",
    base = file("."),
    settings = Project.defaultSettings ++ LeonProject.settings
  ).dependsOn(Github.bonsai, Github.scalaSmtLib)

  object Github {
    def project(repo: String, version: String) = RootProject(uri(s"${repo}#${version}"))

    lazy val bonsai      = project("git://github.com/colder/bonsai.git",     "0fec9f97f4220fa94b1f3f305f2e8b76a3cd1539")
    lazy val scalaSmtLib = project("git://github.com/regb/scala-smtlib.git", "9f88509b13e7e64214c0b9b6a9124fc6c29e2084")
  }
}
