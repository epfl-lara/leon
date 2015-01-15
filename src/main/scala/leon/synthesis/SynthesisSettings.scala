/* Copyright 2009-2014 EPFL, Lausanne */

package leon
package synthesis

import scala.language.existentials
import leon.purescala.Definitions.FunDef

case class SynthesisSettings(
  inPlace: Boolean                    = false,
  allSeeing: Boolean                  = false,
  generateDerivationTrees: Boolean    = false,
  filterFuns: Option[Set[String]]     = None,
  searchWorkers: Int                  = 1,
  firstOnly: Boolean                  = false,
  timeoutMs: Option[Long]             = None,
  costModel: CostModel                = CostModels.default,
  rules: Seq[Rule]                    = Rules.all,
  manualSearch: Option[String]        = None,
  searchBound: Option[Int]            = None,
  selectedSolvers: Set[String]        = Set("fairz3"),
  functionsToIgnore: Set[FunDef]      = Set(),
  
  // Cegis related options
  cegisUseUnsatCores: Boolean         = true,
  cegisUseOptTimeout: Boolean         = true,
  cegisUseBssFiltering: Boolean       = true,
  cegisGenerateFunCalls: Boolean      = true,
  cegisUseCETests: Boolean            = true,
  cegisUseCEPruning: Boolean          = true,
  cegisUseBPaths: Boolean             = true,
  cegisUseVanuatoo: Boolean           = false,

  // Oracles and holes
  distreteHoles: Boolean              = false
)
