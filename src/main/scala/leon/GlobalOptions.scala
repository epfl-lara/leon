/* Copyright 2009-2016 EPFL, Lausanne */

package leon

import leon.utils.{DebugSections, DebugSection}
import OptionParsers._

/** This object contains options that are shared among different modules of Leon.
  *
  * Options that determine the pipeline of Leon are not stored here,
  * but in [[Main.MainComponent]] instead.
  */
object GlobalOptions extends LeonComponent {

  val name = "sharedOptions"
  val description = "Options shared by multiple components of Leon"

  val optStrictPhases = LeonFlagOptionDef("strict", "Terminate after each phase if there is an error", true)

  val optBenchmark    = LeonFlagOptionDef("benchmark", "Dump benchmarking information in a data file", false)

  val optWatch = LeonFlagOptionDef("watch", "Rerun pipeline when file changes", false)

  val optSilent = LeonFlagOptionDef("silent", "Do not display progress messages or  results to the console", false)

  val optFunctions = new LeonOptionDef[Seq[String]] {
    val name = "functions"
    val description = "Only consider functions f1, f2, ..."
    val default = Seq[String]()
    val parser = seqParser(stringParser)
    val usageRhs = "f1,f2,..."
  }

  val optSelectedSolvers = new LeonOptionDef[Set[String]] {
    val name = "solvers"
    val description = "Use solvers s1, s2,...\n" + solvers.SolverFactory.availableSolversPretty
    val default = Set("fairz3")
    val parser = setParser(stringParser)
    val usageRhs = "s1,s2,..."
  }

  val optDebug = new LeonOptionDef[Set[DebugSection]] {
    import OptionParsers._
    val name = "debug"
    val description = {
      val sects = DebugSections.all.toSeq.map(_.name).sorted
      val (first, second) = sects.splitAt(sects.length/2 + 1)
      "Enable detailed messages per component.\nAvailable:\n" +
        "  " + first.mkString(", ") + ",\n" +
        "  " + second.mkString(", ")
    }
    val default = Set[DebugSection]()
    val usageRhs = "d1,d2,..."
    private val debugParser: OptionParser[Set[DebugSection]] = s => {
      if (s == "all") {
        Some(DebugSections.all)
      } else {
        DebugSections.all.find(_.name == s).map(Set(_))
      }
    }
    val parser: String => Option[Set[DebugSection]] = {
      setParser[Set[DebugSection]](debugParser)(_).map(_.flatten)
    }
  }

  val optTimeout = LeonLongOptionDef(
    "timeout",
    "Set a timeout for attempting to prove a verification condition/ repair a function (in sec.)",
    0L,
    "t"
  )

  override val definedOptions: Set[LeonOptionDef[Any]] = Set(
    optStrictPhases,
    optBenchmark,
    optFunctions,
    optSelectedSolvers,
    optDebug,
    optWatch,
    optTimeout,
    optSilent
  )
}
