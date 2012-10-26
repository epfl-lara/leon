name := "Leon"

version := "2.0"

organization := "ch.epfl.lara"

scalaVersion := "2.9.1-1"

scalacOptions += "-deprecation"

scalacOptions += "-unchecked"

libraryDependencies += "org.scala-lang" % "scala-compiler" % "2.9.1-1"

libraryDependencies += "org.scalatest" %% "scalatest" % "1.8" % "test"

if(System.getProperty("sun.arch.data.model") == "64") {
  unmanagedBase <<= baseDirectory { base => base / "unmanaged" / "64" }
} else {
  unmanagedBase <<= baseDirectory { base => base / "unmanaged" / "32" }
}

fork in run := true

fork in test := true
