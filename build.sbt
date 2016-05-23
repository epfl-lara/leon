name := "Leon"

version := "3.0"

organization := "ch.epfl.lara"

val scalaVer = "2.11.8"

scalaVersion := scalaVer

scalacOptions ++= Seq(
  "-deprecation",
  "-unchecked",
  "-feature"
)

scalacOptions in (Compile, doc) ++= Seq("-doc-root-content", baseDirectory.value+"/src/main/scala/root-doc.txt")

javacOptions += "-Xlint:unchecked"

site.settings

site.sphinxSupport()

val osName = Option(System.getProperty("os.name")).getOrElse("").toLowerCase()

val osArch = System.getProperty("sun.arch.data.model")

if(osName.indexOf("win") != -1) {
  (unmanagedJars in Compile) += baseDirectory.value / "unmanaged" / s"scalaz3-win-$osArch.jar"
} else {
  (unmanagedJars in Compile) += baseDirectory.value / "unmanaged" / s"scalaz3-unix-$osArch.jar"
}

unmanagedBase <<= baseDirectory { base => base / "unmanaged" / osArch }

resolvers ++= Seq(
  "Typesafe Repository" at "http://repo.typesafe.com/typesafe/releases/",
  "Sonatype OSS Snapshots" at "https://oss.sonatype.org/content/repositories/snapshots",
  "Sonatype OSS Releases" at "https://oss.sonatype.org/content/repositories/releases"
)

val libisabelleVer = "0.3.1"

libraryDependencies ++= Seq(
  "org.scala-lang" % "scala-compiler" % scalaVer,
  "org.scalatest" %% "scalatest" % "2.2.4" % "test",
  "com.typesafe.akka" %% "akka-actor" % "2.3.4",
  "info.hupel" %% "libisabelle" % libisabelleVer,
  "info.hupel" %% "libisabelle-setup" % libisabelleVer,
  "info.hupel" %% "slf4j-impl-helper" % "0.1" % "optional",
  "org.ow2.asm" % "asm-all" % "5.0.4",
  "com.fasterxml.jackson.module" %% "jackson-module-scala" % "2.6.0-rc2"//,
  //"com.regblanc" %% "scala-smtlib" % "0.2"
)

lazy val scriptName = "leon"

lazy val scriptFile = file(".") / scriptName

clean := {
  clean.value
  if(scriptFile.exists && scriptFile.isFile) {
    scriptFile.delete
  }
}

lazy val nParallel = {
  val p = System.getProperty("parallel")
  if (p ne null) {
    try {
      p.toInt
    } catch {
      case nfe: NumberFormatException =>
        1
    }
  } else {
    1
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
    IO.write(f, s"""|#!/bin/bash --posix
                    |
                    |SCALACLASSPATH="$paths"
                    |
                    |java -Xmx2G -Xms512M -Xss64M -classpath "$${SCALACLASSPATH}" -Dscala.usejavacp=false scala.tools.nsc.MainGenericRunner -classpath "$${SCALACLASSPATH}" leon.Main $$@ 2>&1 | tee -i last.log
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
                      |    ${libFiles.mkString("\"\"\"", "\"\"\",\n    \"\"\"", "\"\"\"").replaceAll("\\\\"+"u","\\\\\"\"\"+\"\"\"u")}
                      |  )
                      |}""".stripMargin)
  Seq(build)
}


sourcesInBase in Compile := false

Keys.fork in run := true


lazy val testSettings = Seq(
    //Keys.fork := true,
    logBuffered := (nParallel > 1),
    parallelExecution := (nParallel > 1)
    //testForkedParallel := true,
    //javaOptions ++= Seq("-Xss64M", "-Xmx4G")
)

concurrentRestrictions in Global += Tags.limit(Tags.Test, nParallel)

// Unit Tests
testOptions in Test := Seq(Tests.Argument("-oDF"), Tests.Filter(_ startsWith "leon.unit."))

// Integration Tests
lazy val IntegrTest = config("integration") extend(Test)

testOptions in IntegrTest := Seq(Tests.Argument("-oDF"), Tests.Filter(_ startsWith "leon.integration."))


def regressionFilter(name: String, native: Boolean = false): Boolean = name.startsWith("leon.regression") && (name.endsWith("NativeZ3") == native)

// Regression Tests
lazy val RegressionTest = config("regression") extend(Test)

testOptions in RegressionTest := Seq(Tests.Argument("-oDF"), Tests.Filter(regressionFilter(_)))

// Regression Tests that heavily depend on native Z3
lazy val NativeZ3RegressionTest = config("native") extend(Test)

testOptions in NativeZ3RegressionTest := Seq(Tests.Argument("-oDF"), Tests.Filter(regressionFilter(_, native = true)))

parallelExecution in NativeZ3RegressionTest := false

logBuffered in NativeZ3RegressionTest := false


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
lazy val scalaSmtlib = ghProject("git://github.com/regb/scala-smtlib.git", "88835c02ca2528e888b06bc48e4e93e52dc5f4b5")
lazy val cafebabe    = ghProject("git://github.com/psuter/cafebabe.git",   "49dce3c83450f5fa0b5e6151a537cc4b9f6a79a6")

lazy val root = (project in file(".")).
  configs(RegressionTest, NativeZ3RegressionTest, IsabelleTest, GenCTest, IntegrTest).
  dependsOn(bonsai).
  dependsOn(scalaSmtlib).
  dependsOn(cafebabe).
  settings(inConfig(NativeZ3RegressionTest)(Defaults.testTasks ++ testSettings): _*).
  settings(inConfig(RegressionTest)(Defaults.testTasks ++ testSettings): _*).
  settings(inConfig(IntegrTest)(Defaults.testTasks ++ testSettings): _*).
  settings(inConfig(IsabelleTest)(Defaults.testTasks ++ testSettings): _*).
  settings(inConfig(GenCTest)(Defaults.testTasks ++ testSettings): _*).
  settings(inConfig(Test)(Defaults.testTasks ++ testSettings): _*)

