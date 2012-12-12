import sbt._
import Keys._
import PlayProject._

object ApplicationBuild extends Build {

    val appName         = "leononline"
    val appVersion      = "1.0-SNAPSHOT"

    val appDependencies = Seq(
      "org.scala-lang" % "scala-compiler" % "2.9.1"
    )

    val main = PlayProject(appName, appVersion, appDependencies, mainLang = SCALA).settings(
      // Add your own project settings here      
    )

}
