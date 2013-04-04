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

  // Cegis related options
  cegisGenerateFunCalls: Boolean      = false,
  cegisUseCETests: Boolean            = true,
  cegisUseCEPruning: Boolean          = true,
  cegisUseBPaths: Boolean             = true
)
