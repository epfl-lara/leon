name := "Leon"

version := "2.3"

organization := "ch.epfl.lara"

scalaVersion := "2.11.2"

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
    "org.scala-lang" % "scala-compiler" % "2.11.2",
    "org.scalatest" %% "scalatest" % "2.2.0" % "test",
    "com.typesafe.akka" %% "akka-actor" % "2.3.4"
)

Keys.fork in run := true

Keys.fork in Test := true

logBuffered in Test := false

testOptions in Test += Tests.Argument("-oDF")

javaOptions in Test += "-Xss32M"

parallelExecution in test := false

sourcesInBase in Compile := false
