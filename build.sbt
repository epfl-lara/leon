name := "Leon"

version := "2.0"

organization := "ch.epfl.lara"

scalaVersion := "2.10.2"

scalacOptions += "-deprecation"

scalacOptions += "-unchecked"

scalacOptions += "-feature"

javacOptions += "-Xlint:unchecked"

if(System.getProperty("sun.arch.data.model") == "64") {
  unmanagedBase <<= baseDirectory { base => base / "unmanaged" / "64" }
} else {
  unmanagedBase <<= baseDirectory { base => base / "unmanaged" / "32" }
}

resolvers += "Typesafe Repository" at "http://repo.typesafe.com/typesafe/releases/"

libraryDependencies ++= Seq(
    "org.scala-lang" % "scala-compiler" % "2.10.2",
    "org.scalatest" % "scalatest_2.10" % "2.0.M5b" % "test" excludeAll(ExclusionRule(organization="org.scala-lang")),
    "com.typesafe.akka" %% "akka-actor" % "2.2.0" excludeAll(ExclusionRule(organization="org.scala-lang"))
)

fork in run := true

fork in test := true

logBuffered in Test := false

testOptions in Test += Tests.Argument("-oD")
