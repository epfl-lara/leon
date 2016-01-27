name := "Leon"

version := "3.0"

organization := "ch.epfl.lara"

scalaVersion := "2.11.7"

scalacOptions ++= Seq(
  "-deprecation",
  "-unchecked",
  "-feature"
)

scalacOptions in (Compile, doc) ++= Seq("-doc-root-content", baseDirectory.value+"/src/main/scala/root-doc.txt")

javacOptions += "-Xlint:unchecked"

site.settings

site.sphinxSupport()

if(System.getProperty("sun.arch.data.model") == "64") {
  unmanagedBase <<= baseDirectory { base => base / "unmanaged" / "64" }
} else {
  unmanagedBase <<= baseDirectory { base => base / "unmanaged" / "32" }
}

resolvers ++= Seq(
  "Typesafe Repository" at "http://repo.typesafe.com/typesafe/releases/",
  "Sonatype OSS Snapshots" at "https://oss.sonatype.org/content/repositories/snapshots"
)

val libisabelleVersion = "0.2"

libraryDependencies ++= Seq(
  "org.scala-lang" % "scala-compiler" % "2.11.7",
  "org.scalatest" %% "scalatest" % "2.2.4" % "test",
  "com.typesafe.akka" %% "akka-actor" % "2.3.4",
  "info.hupel" %% "libisabelle" % libisabelleVersion,
  "info.hupel" %% "libisabelle-setup" % libisabelleVersion,
  "info.hupel" %% "pide-2015" % libisabelleVersion,
  "org.slf4j" % "slf4j-nop" % "1.7.13",
  "org.ow2.asm" % "asm-all" % "5.0.4",
  "com.fasterxml.jackson.module" %% "jackson-module-scala" % "2.6.0-rc2"
)

lazy val scriptName = "leon"

lazy val scriptFile = file(".") / scriptName

clean := {
  clean.value
  if(scriptFile.exists && scriptFile.isFile) {
    scriptFile.delete
  }
}

lazy val script = taskKey[Unit]("Generate the leon Bash script")

script := {
  val s = streams.value
  try {
    val cps = (dependencyClasspath in Compile).value
    val out = (classDirectory      in Compile).value
    val res = (resourceDirectory   in Compile).value
    val is64 = System.getProperty("sun.arch.data.model") == "64"
    val f = scriptFile
    if(f.exists) {
      s.log.info("Regenerating '"+f.getName+"' script ("+(if(is64) "64b" else "32b")+")...")
      f.delete
    } else {
      s.log.info("Generating '"+f.getName+"' script ("+(if(is64) "64b" else "32b")+")...")
    }
    val paths = (res.getAbsolutePath +: out.getAbsolutePath +: cps.map(_.data.absolutePath)).mkString(System.getProperty("path.separator"))
    val base = baseDirectory.value.getAbsolutePath
    IO.write(f, s"""|#!/bin/bash --posix
                    |
                    |SCALACLASSPATH="$paths"
                    |BASEDIRECTORY="$base"
                    |
                    |java -Xmx2G -Xms512M -Xss64M -classpath "$${SCALACLASSPATH}" -Dleon.base="$${BASEDIRECTORY}" -Dscala.usejavacp=false scala.tools.nsc.MainGenericRunner -classpath "$${SCALACLASSPATH}" leon.Main $$@ 2>&1 | tee -i last.log
                    |""".stripMargin)
    f.setExecutable(true)
  } catch {
    case e: Throwable =>
      s.log.error("There was an error while generating the script file: " + e.getLocalizedMessage)
  }
}

sourceGenerators in Compile <+= Def.task {
  val libFiles = ((baseDirectory.value / "library") ** "*.scala").getPaths
  val build = (sourceManaged in Compile).value / "leon" / "Build.scala";
  IO.write(build, s"""|package leon
                      |
                      |object Build {
                      |  val baseDirectory = \"\"\"${baseDirectory.value.toString}\"\"\"
                      |  val libFiles = List(
                      |    ${libFiles.mkString("\"\"\"", "\"\"\",\n    \"\"\"", "\"\"\"")}
                      |  )
                      |}""".stripMargin)
  Seq(build)
}


sourcesInBase in Compile := false

Keys.fork in run := true

lazy val testSettings = Seq(
    //Keys.fork := true,
    logBuffered := true,
    parallelExecution := true
    //testForkedParallel := true,
    //javaOptions ++= Seq("-Xss64M", "-Xmx4G")
)

// Unit Tests
testOptions in Test := Seq(Tests.Argument("-oDF"), Tests.Filter(_ startsWith "leon.unit."))

// Integration Tests
lazy val IntegrTest = config("integration") extend(Test)

testOptions in IntegrTest := Seq(Tests.Argument("-oDF"), Tests.Filter(_ startsWith "leon.integration."))



// Regression Tests
lazy val RegressionTest = config("regression") extend(Test)

testOptions in RegressionTest := Seq(Tests.Argument("-oDF"), Tests.Filter(_ startsWith "leon.regression."))



// Isabelle Tests
lazy val IsabelleTest = config("isabelle") extend(Test)

testOptions in IsabelleTest := Seq(Tests.Argument("-oDF"), Tests.Filter(_ startsWith "leon.isabelle."))

parallelExecution in IsabelleTest := false

fork in IsabelleTest := true

// GenC Tests
lazy val GenCTest = config("genc") extend(Test)

testOptions in GenCTest := Seq(Tests.Argument("-oDF"), Tests.Filter(_ startsWith "leon.genc."))

parallelExecution in GenCTest := false



def ghProject(repo: String, version: String) = RootProject(uri(s"${repo}#${version}"))

lazy val bonsai      = ghProject("git://github.com/colder/bonsai.git",     "10eaaee4ea0ff6567f4f866922cb871bae2da0ac")
lazy val scalaSmtLib = ghProject("git://github.com/regb/scala-smtlib.git", "372bb14d0c84953acc17f9a7e1592087adb0a3e1")

lazy val root = (project in file(".")).
  configs(RegressionTest, IsabelleTest, GenCTest, IntegrTest).
  dependsOn(bonsai, scalaSmtLib).
  settings(inConfig(RegressionTest)(Defaults.testTasks ++ testSettings): _*).
  settings(inConfig(IntegrTest)(Defaults.testTasks ++ testSettings): _*).
  settings(inConfig(IsabelleTest)(Defaults.testTasks ++ testSettings): _*).
  settings(inConfig(GenCTest)(Defaults.testTasks ++ testSettings): _*).
  settings(inConfig(Test)(Defaults.testTasks ++ testSettings): _*)

