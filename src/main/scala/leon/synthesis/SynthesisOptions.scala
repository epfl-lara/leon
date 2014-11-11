/* Copyright 2009-2014 EPFL, Lausanne */

package leon
package synthesis

import scala.language.existentials

case class SynthesisOptions(
  inPlace: Boolean                    = false,
  allSeeing: Boolean                  = false,
  generateDerivationTrees: Boolean    = false,
  filterFuns: Option[Set[String]]     = None,
  searchWorkers: Int                  = 1,
  firstOnly: Boolean                  = false,
  timeoutMs: Option[Long]             = None,
  costModel: CostModel                = CostModels.default,
  rules: Seq[Rule]                    = Rules.all ++ Heuristics.all,
  manualSearch: Boolean               = false,
  searchBound: Option[Int]            = None,
  selectedSolvers: Set[String]        = Set("fairz3"),

  // Cegis related options
  cegisUseUninterpretedProbe: Boolean = false,
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
