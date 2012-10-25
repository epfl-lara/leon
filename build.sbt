name := "Leon"

version := "2.0"

organization := "ch.epfl.lara"

scalaVersion := "2.9.1-1"

scalacOptions += "-deprecation"

scalacOptions += "-unchecked"

libraryDependencies += "org.scala-lang" % "scala-compiler" % "2.9.1-1"

libraryDependencies += "org.scalatest" %% "scalatest" % "1.8" % "test"

unmanagedBase <<= baseDirectory { base => base / "unmanaged" }

fork in run := true

fork in test := true
