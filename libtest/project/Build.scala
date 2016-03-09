import sbt._
import Keys._

object BuildSettings {
  val paradiseVersion = "2.1.0-M5"
  val buildSettings = Defaults.defaultSettings ++ Seq(
    resolvers += Resolver.sonatypeRepo("snapshots"),
    resolvers += Resolver.sonatypeRepo("releases"),
    addCompilerPlugin("org.scalamacros" % "paradise" % paradiseVersion cross CrossVersion.full)
  )
}

object MyBuild extends Build {
  import BuildSettings._

  lazy val root = Project(
    "root",
    file("."),
    settings = buildSettings
  ) 
  
//  aggregate (macros, benchmarks)
//
//  lazy val macros = Project(
//    "leon",
//    file("src/main/scala/leon"),
//    settings = buildSettings 
//  )
//  
//  lazy val benchmarks = Project(
//    "benchmark",
//    file("src/main/scala/benchmarks"),
//    settings = buildSettings 
//  ) dependsOn macros
}
