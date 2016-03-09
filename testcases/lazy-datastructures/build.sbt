name := "LazyDataStructures"

version := "1.0"

organization := "ch.epfl.lara"

scalaVersion := "2.11.7"

fork in run := true

javaOptions in run ++= Seq("-Xmx5G", "-Xms3G", "-Xss500M")

scalacOptions ++= Seq("-optimise")

unmanagedSourceDirectories in Compile ++= Seq("withOrb", "eager").map(dir => baseDirectory.value / dir)
