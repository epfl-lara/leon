/* Copyright 2009-2015 EPFL, Lausanne */

package leon

import leon.utils.{DebugSections, DebugSection}
import OptionParsers._

object SharedOptions extends LeonComponent {

  val name = "sharedOptions"
  val description = "Options shared by multiple components of Leon"

  val optStrictPhases = LeonFlagOptionDef("strict", "Terminate after each phase if there is an error", true)

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
    val description = "Enable detailed messages per component"
    val default = Set[DebugSection]()
    val usageRhs = "d1,d2,..."
    val debugParser: OptionParser[Set[DebugSection]] = s => {
      if (s == "all") {
        DebugSections.all
      } else {
        DebugSections.all.find(_.name == s) match {
          case Some(rs) =>
            Set(rs)
          case None =>
            throw new IllegalArgumentException
          //initReporter.error("Section "+s+" not found, available: "+DebugSections.all.map(_.name).mkString(", "))
          //Set()
        }
      }
    }
    val parser: String => Set[DebugSection] = setParser[Set[DebugSection]](debugParser)(_).flatten
  }

  val optTimeout = LeonLongOptionDef("timeout", "Set a timeout for each verification/repair (in sec.)", 0L, "t")

  override val definedOptions: Set[LeonOptionDef[Any]] = Set(
    optStrictPhases,
    optFunctions,
    optSelectedSolvers,
    optDebug,
    optTimeout
  )
}
