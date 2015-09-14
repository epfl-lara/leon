package leon.solvers.isabelle

import java.nio.file.Paths

import scala.concurrent._
import scala.concurrent.duration._
import scala.concurrent.ExecutionContext.Implicits.global

import leon._

object Component extends LeonComponent {

  val name = "isabelle"
  val description = "Isabelle solver"

  val leonBase =
    Paths.get(Option(System.getProperty("leon.base")).getOrElse(".")).toAbsolutePath()

  val isabelleBase =
    leonBase.resolve("contrib").toAbsolutePath()

  val optBase = LeonStringOptionDef(
    name = "isabelle:base",
    description = "Base directory of the Isabelle installation",
    default = isabelleBase.toString,
    usageRhs = "path"
  )

  val optDownload = LeonFlagOptionDef(
    name = "isabelle:download",
    description = "Automatic download of Isabelle",
    default = false
  )

  val optBuild = LeonFlagOptionDef(
    name = "isabelle:build",
    description = "Automatic build of Isabelle/Leon",
    default = true
  )

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
    Set(optBase, optDownload, optBuild, optMapping, optDump, optStrict)

}
