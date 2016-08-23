/* Copyright 2009-2016 EPFL, Lausanne */

package leon.solvers.isabelle

import java.nio.file.Paths

import scala.concurrent._
import scala.concurrent.duration._
import scala.concurrent.ExecutionContext.Implicits.global

import leon._

import info.hupel.isabelle.setup._

object Component extends LeonComponent {

  val name = "Isabelle"
  val description = "Isabelle solver"

  def platform =
    Platform.guess.getOrElse(sys.error("Unknown platform; can't run Isabelle here"))

  val optMapping = LeonFlagOptionDef(
    name = "isabelle:mapping",
    description = "Enable processing of type and function mapping annotations",
    default = true
  )

  val optDump = LeonStringOptionDef(
    name = "isabelle:dump",
    description = "Dump theory source files into the specified directory",
    default = "",
    usageRhs = "path"
  )

  val optStrict = LeonFlagOptionDef(
    name = "isabelle:strict",
    description = "Require proofs for indirectly referenced functions",
    default = true
  )

  override val definedOptions: Set[LeonOptionDef[Any]] =
    Set(optMapping, optDump, optStrict)

}
