enablePlugins(ScalaJSPlugin)

name := "Leon-TicTacToe"

scalaVersion := "2.11.7"

libraryDependencies += "org.scala-js" %%% "scalajs-dom" % "0.9.0"

unmanagedSourceDirectories in Compile += (baseDirectory / "../../library/leon/").value
