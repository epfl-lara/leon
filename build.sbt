name := "Leon"

version := "2.3"

organization := "ch.epfl.lara"

scalaVersion := "2.11.1"

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
    "org.scala-lang" % "scala-compiler" % "2.11.1",
    "org.scalatest" %% "scalatest" % "2.2.0" % "test",
    "com.typesafe.akka" %% "akka-actor" % "2.3.4"
)

Keys.fork in run := true

Keys.fork in test := true

logBuffered in test := false

testOptions in test += Tests.Argument("-oD")

javaOptions in test += "-Xss32M"

parallelExecution in test := false

sourcesInBase in Compile := false
