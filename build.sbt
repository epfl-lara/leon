name := "Leon"

version := "3.0"

organization := "ch.epfl.lara"

scalaVersion := "2.11.6"

scalacOptions ++= Seq(
  "-deprecation",
  "-unchecked",
  "-feature"
)

scalacOptions in (Compile, doc) ++= Seq("-doc-root-content", baseDirectory.value+"/src/main/scala/root-doc.txt")

javacOptions += "-Xlint:unchecked"

if(System.getProperty("sun.arch.data.model") == "64") {
  unmanagedBase <<= baseDirectory { base => base / "unmanaged" / "64" }
} else {
  unmanagedBase <<= baseDirectory { base => base / "unmanaged" / "32" }
}

resolvers ++= Seq(
  "Typesafe Repository" at "http://repo.typesafe.com/typesafe/releases/",
  "Sonatype OSS Snapshots" at "https://oss.sonatype.org/content/repositories/snapshots"
)

libraryDependencies ++= Seq(
  "org.scala-lang" % "scala-compiler" % "2.11.6",
  "org.scalatest" %% "scalatest" % "2.2.0" % "test",
  "com.typesafe.akka" %% "akka-actor" % "2.3.4",
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

sourceGenerators in Compile <+= Def.task {
  val libFiles = ((baseDirectory.value / "library") ** "*.scala").getPaths
  val build = (sourceManaged in Compile).value / "leon" / "Build.scala";
  IO.write(build, s"""|package leon;
                    |
                    |object Build {
                    |  val libFiles = List(
                    |    ${libFiles.mkString("\"\"\"", "\"\"\",\n    \"\"\"", "\"\"\"")}
                    |  )
                    |}""".stripMargin)
  Seq(build)
}


sourcesInBase in Compile := false

Keys.fork in run := true

lazy val testSettings = Seq(
    Keys.fork := true,
    logBuffered := false,
    javaOptions ++= Seq("-Xss16M", "-Xmx4G", "-XX:MaxPermSize=128M")
)

// Unit Tests
testOptions in Test := Seq(Tests.Argument("-oDF"), Tests.Filter(_ startsWith "leon.unit."))

// Integration Tests
lazy val IntegrTest = config("integration") extend(Test)

testOptions in IntegrTest := Seq(Tests.Argument("-oDF"), Tests.Filter(_ startsWith "leon.integration."))



// RegressionTest Tests
lazy val RegressionTest = config("regression") extend(Test)

testOptions in RegressionTest  := Seq(Tests.Argument("-oDF"), Tests.Filter(_ startsWith "leon.regression."))

parallelExecution in RegressionTest := false


def ghProject(repo: String, version: String) = RootProject(uri(s"${repo}#${version}"))

lazy val bonsai      = ghProject("git://github.com/colder/bonsai.git",     "0fec9f97f4220fa94b1f3f305f2e8b76a3cd1539")

lazy val scalaSmtLib = RootProject(new File("/home/ekneuss/git/scala-smtlib"))//ghProject("git://github.com/regb/scala-smtlib.git", "26f4ad48cb5b1bf46bd3630b9fd877abbafe6983")

lazy val root = (project in file(".")).
  configs(RegressionTest).
  configs(IntegrTest).
  dependsOn(bonsai, scalaSmtLib).
  settings(inConfig(RegressionTest)(Defaults.testTasks ++ testSettings): _*).
  settings(inConfig(IntegrTest)(Defaults.testTasks ++ testSettings): _*)


