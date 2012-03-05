name := "Leon"

version := "2.0"

organization := "ch.epfl.lara"

scalaVersion := "2.9.0-1"

scalacOptions += "-deprecation"

scalacOptions += "-unchecked"

libraryDependencies += "org.scala-lang" % "scala-compiler" % "2.9.0-1"

unmanagedBase <<= baseDirectory { base => base / "unmanaged" }

