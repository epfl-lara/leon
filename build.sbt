name := "Leon"

version := "3.0"

organization := "ch.epfl.lara"

scalaVersion := "2.11.6"

scalacOptions ++= Seq(
    "-deprecation",
    "-unchecked",
    "-feature"
)

javacOptions += "-Xlint:unchecked"


if(System.getProperty("sun.arch.data.model") == "64") {
  unmanagedBase <<= baseDirectory { base => base / "unmanaged" / "64" }
} else {
  unmanagedBase <<= baseDirectory { base => base / "unmanaged" / "32" }
}

resolvers += "Typesafe Repository" at "http://repo.typesafe.com/typesafe/releases/"

libraryDependencies ++= Seq(
    "org.scala-lang" % "scala-compiler" % "2.11.6",
    "org.scalatest" %% "scalatest" % "2.2.0" % "test",
    "com.typesafe.akka" %% "akka-actor" % "2.3.4"
)

Keys.fork in run := true

Keys.fork in Test := true

logBuffered in Test := false

javaOptions in Test ++= Seq("-Xss32M", "-Xmx4G", "-XX:MaxPermSize=128M")

parallelExecution in Test := false

testOptions in (Test, test) := Seq(Tests.Filter(s => s.endsWith("LeonAllTests")), Tests.Argument("-oDF"))

testOptions in (Test, testOnly) := Seq(Tests.Argument("-oDF"))

sourcesInBase in Compile := false
