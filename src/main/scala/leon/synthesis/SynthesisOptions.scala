/* Copyright 2009-2013 EPFL, Lausanne */

package leon
package synthesis

case class SynthesisOptions(
  inPlace: Boolean                    = false,
  generateDerivationTrees: Boolean    = false,
  filterFuns: Option[Set[String]]     = None,
  searchWorkers: Int                  = 1,
  firstOnly: Boolean                  = false,
  timeoutMs: Option[Long]             = None,
  costModel: CostModel                = CostModel.default,
  rules: Seq[Rule]                    = Rules.all ++ Heuristics.all,
  manualSearch: Boolean               = false,
  searchBound: Option[Int]            = None,

  // Cegis related options
  cegisUseUninterpretedProbe: Boolean = false,
  cegisUseUnsatCores: Boolean         = true,
  cegisUseOptTimeout: Boolean         = true,
  cegisUseBssFiltering: Boolean       = true,
  cegisGenerateFunCalls: Boolean      = true,
  cegisUseCETests: Boolean            = true,
  cegisUseCEPruning: Boolean          = true,
  cegisUseBPaths: Boolean             = true,
  cegisUseVanuatoo: Boolean           = false
)
